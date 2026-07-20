/**
 * The sole Pi extension allowed in a Harness v2 proof Job.
 *
 * Pi owns the agent loop and OpenAI-compatible streaming. Every model-callable
 * operation crosses the engine-owned Unix-socket broker. The extension never
 * starts an interpreter or receives host-side lease, checkout, or output paths.
 */

import { createHash } from "node:crypto";
import {
	closeSync,
	constants,
	fstatSync,
	lstatSync,
	openSync,
	readFileSync,
	realpathSync,
	writeSync,
} from "node:fs";
import { createConnection } from "node:net";
import { isAbsolute, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { TextDecoder } from "node:util";
import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";
import { Type } from "typebox";

const PROVIDER = "harness-leanstral";
const TOOLS = [
	"read_context",
	"search_symbol",
	"apply_patch_scoped",
	"lean_check",
	"git_diff",
	"report_blocked",
] as const;
const TOOL_SET = new Set<string>(TOOLS);

const PUBLIC_CONFIG_SCHEMA = "poincare.pi-public-config.v2";
const RPC_SCHEMA = "poincare.pi-rpc.v1";
const SEALED_PUBLIC_CONFIG_PATH = "/sealed/public-config.json";
const SEALED_SYSTEM_PROMPT_PATH = "/sealed/system-prompt.md";
const SEALED_EXTENSION_PATH = "/sealed/extension.ts";
const SEALED_SETTINGS_PATH = "/sealed/agent/settings.json";
const SEALED_AGENT_DIR = "/sealed/agent";
const BROKER_SOCKET_ENV = "HARNESS_PI_BROKER_SOCKET";
const BROKER_TOKEN_ENV = "HARNESS_PI_BROKER_TOKEN";
const CONTEXT_WINDOW = 200_000;

const PUBLIC_CONFIG_KEYS = [
	"schema_version",
	"job_id",
	"session_id",
	"backend",
	"extension_sha256",
	"output_token_budget",
	"prompt_sha256",
	"prompt_size_bytes",
	"system_prompt_path",
	"system_prompt_sha256",
	"settings_path",
	"settings_sha256",
	"broker",
] as const;
const BACKEND_KEYS = ["kind", "model", "model_revision", "endpoint", "sampling"] as const;
const SAMPLING_KEYS = ["max_tokens", "temperature"] as const;
const BROKER_KEYS = ["socket_env", "token_env"] as const;
const RPC_REQUEST_KEYS = [
	"protocol",
	"job_id",
	"session_id",
	"sequence",
	"tool_call_id",
	"tool",
	"token",
	"params",
] as const;
const RPC_RESPONSE_KEYS = [
	"protocol",
	"job_id",
	"session_id",
	"sequence",
	"tool_call_id",
	"ok",
	"result",
	"error",
] as const;
const RPC_RESULT_KEYS = ["text"] as const;
const RPC_RESULT_WITH_DETAILS_KEYS = ["text", "details"] as const;

const MAX_PUBLIC_CONFIG_BYTES = 128 * 1024;
const MAX_SYSTEM_PROMPT_BYTES = 1024 * 1024;
const MAX_EXTENSION_BYTES = 2 * 1024 * 1024;
const MAX_SETTINGS_BYTES = 64 * 1024;
const MAX_RPC_REQUEST_BYTES = 768 * 1024;
const MAX_RPC_RESPONSE_BYTES = 2 * 1024 * 1024;
const RPC_TIMEOUT_MS = 30_000;
const MAX_TRACKED_CALL_IDS = 100_000;
const FAIL_CLOSED_EXIT_CODE = 70;
const MAX_INVARIANT_MESSAGE_CHARS = 4_096;

type Backend = {
	kind: string;
	model: string;
	model_revision: string;
	endpoint: string;
	sampling: {
		max_tokens: unknown;
		temperature: unknown;
	};
};

type PublicConfig = {
	schema_version: typeof PUBLIC_CONFIG_SCHEMA;
	job_id: string;
	session_id: string;
	backend: Backend;
	extension_sha256: string;
	output_token_budget: number;
	prompt_sha256: string;
	prompt_size_bytes: number;
	system_prompt_path: typeof SEALED_SYSTEM_PROMPT_PATH;
	system_prompt_sha256: string;
	settings_path: typeof SEALED_SETTINGS_PATH;
	settings_sha256: string;
	broker: {
		socket_env: typeof BROKER_SOCKET_ENV;
		token_env: typeof BROKER_TOKEN_ENV;
	};
};

type BrokerReply = {
	ok: true;
	text: string;
	details?: unknown;
};

type Runtime = {
	config: PublicConfig;
	configHash: string;
	extensionHash: string;
	systemPromptHash: string;
	systemPrompt: string;
	settingsHash: string;
	socketPath: string;
	socketDevice: number;
	socketInode: number;
	token: string;
};

const PRIVATE_SETTINGS_BYTES = Buffer.from(
	'{"compaction":{"enabled":false}}',
	"utf8",
);

let nextSequence = 1;
const usedToolCallIds = new Set<string>();

function requiredEnv(name: string): string {
	const value = process.env[name];
	if (!value) throw new Error(`Harness Pi extension requires ${name}`);
	if (value.includes("\n") || value.includes("\r") || value.includes("\0")) {
		throw new Error(`Harness Pi extension rejected malformed ${name}`);
	}
	return value;
}

function sha256(data: Buffer): string {
	return createHash("sha256").update(data).digest("hex");
}

function isRecord(value: unknown): value is Record<string, unknown> {
	return typeof value === "object" && value !== null && !Array.isArray(value);
}

function failClosedInvariant(error: unknown): never {
	let detail = "unprintable invariant failure";
	try {
		detail = String(error instanceof Error ? error.message : error);
	} catch {
		// Keep the non-empty fallback above.
	}
	detail = detail.replace(/[\0\r\n]+/g, " ").slice(0, MAX_INVARIANT_MESSAGE_CHARS);
	try {
		// Pi 0.80.10 catches extension-handler exceptions. A synchronous fd write
		// followed by process.exit stays outside that catch boundary.
		writeSync(2, `Harness Pi invariant failure: ${detail || "unknown failure"}\n`);
	} catch {
		// An unavailable stderr must not turn a security invariant into fail-open.
	}
	process.exit(FAIL_CLOSED_EXIT_CODE);
}

function enforceInvariant<T>(check: () => T): T {
	try {
		return check();
	} catch (error) {
		return failClosedInvariant(error);
	}
}

function assertExactKeys(
	value: unknown,
	keys: readonly string[],
	label: string,
): asserts value is Record<string, unknown> {
	if (!isRecord(value)) throw new Error(`${label} must be an object`);
	const actual = Object.keys(value).sort();
	const expected = [...keys].sort();
	if (JSON.stringify(actual) !== JSON.stringify(expected)) {
		throw new Error(`${label} fields do not match the exact contract`);
	}
}

function checkedHash(value: unknown, label: string): string {
	if (typeof value !== "string" || !/^[0-9a-f]{64}$/.test(value)) {
		throw new Error(`${label} has an invalid SHA-256`);
	}
	return value;
}

function nonnegativeInteger(value: unknown, label: string): number {
	if (typeof value !== "number" || !Number.isSafeInteger(value) || value < 0) {
		throw new Error(`${label} must be a nonnegative safe integer`);
	}
	return value;
}

export function assertPromptIdentity(
	prompt: unknown,
	expectedSha256: string,
	expectedSizeBytes: number,
): void {
	if (typeof prompt !== "string") {
		throw new Error("Harness Pi prompt must be a string");
	}
	assertWellFormedUnicode(prompt, "Harness Pi prompt");
	const bytes = Buffer.from(prompt, "utf8");
	if (bytes.length !== expectedSizeBytes || sha256(bytes) !== expectedSha256) {
		throw new Error("Harness Pi prompt bytes do not match the sealed Job snapshot");
	}
}

function assistantUsageOutput(message: unknown, final: boolean): number {
	if (!isRecord(message) || message.role !== "assistant" || !isRecord(message.usage)) {
		throw new Error("Harness Pi assistant message is missing provider usage");
	}
	const output = nonnegativeInteger(
		message.usage.output,
		"Harness Pi assistant output-token usage",
	);
	if (final && output === 0) {
		throw new Error("Harness Pi final assistant message has untrusted zero usage");
	}
	return output;
}

/**
 * Trusted per-Job accounting. Pi's provider clamp is an input to this tracker,
 * never a value the extension may raise. Usage is cumulative per provider
 * response and is committed exactly once at message_end.
 */
export class HarnessOutputBudget {
	private readonly perRequestMaximum: number;
	private readonly totalBudget: number;
	private committed = 0;
	private activeLimit: number | undefined;
	private activeObserved = 0;

	constructor(perRequestMaximum: number, totalBudget: number) {
		this.perRequestMaximum = positiveInteger(
			perRequestMaximum,
			"Harness Pi per-request output-token maximum",
		);
		this.totalBudget = positiveInteger(
			totalBudget,
			"Harness Pi cumulative output-token budget",
		);
		if (this.perRequestMaximum > this.totalBudget) {
			throw new Error("Harness Pi per-request maximum exceeds the Job budget");
		}
	}

	beginRequest(upstreamPiLimit: unknown): number {
		if (this.activeLimit !== undefined) {
			throw new Error("Harness Pi observed overlapping provider requests");
		}
		const upstream = positiveInteger(
			upstreamPiLimit,
			"Harness Pi upstream provider max_tokens",
		);
		const remaining = this.totalBudget - this.committed;
		if (remaining <= 0) {
			throw new Error("Harness Pi cumulative output-token budget is exhausted");
		}
		const effective = Math.min(upstream, this.perRequestMaximum, remaining);
		this.activeLimit = effective;
		this.activeObserved = 0;
		return effective;
	}

	observe(message: unknown): void {
		if (this.activeLimit === undefined) {
			throw new Error("Harness Pi observed assistant output without a provider request");
		}
		const output = assistantUsageOutput(message, false);
		if (output < this.activeObserved) {
			throw new Error("Harness Pi streaming output-token usage moved backwards");
		}
		if (
			output > this.activeLimit ||
			this.committed + output > this.totalBudget
		) {
			throw new Error("Harness Pi streaming output exceeded its sealed token cap");
		}
		this.activeObserved = output;
	}

	complete(message: unknown): void {
		if (this.activeLimit === undefined) {
			throw new Error("Harness Pi completed assistant output without a provider request");
		}
		const output = assistantUsageOutput(message, true);
		if (output < this.activeObserved) {
			throw new Error("Harness Pi final output-token usage moved backwards");
		}
		if (
			output > this.activeLimit ||
			this.committed + output > this.totalBudget
		) {
			throw new Error("Harness Pi final output exceeded its sealed token cap");
		}
		this.committed += output;
		this.activeLimit = undefined;
		this.activeObserved = 0;
	}

	assertSettled(): void {
		if (this.activeLimit !== undefined) {
			throw new Error("Harness Pi settled with an unaccounted provider request");
		}
	}

	get committedOutputTokens(): number {
		return this.committed;
	}
}

function checkedString(value: unknown, label: string, maxLength = 4096): string {
	if (
		typeof value !== "string" ||
		value.length < 1 ||
		value.length > maxLength ||
		/[\0\r\n]/.test(value)
	) {
		throw new Error(`${label} must be a bounded single-line string`);
	}
	return value;
}

function checkedJobId(value: unknown): string {
	if (typeof value !== "string" || !/^[a-z0-9][a-z0-9._-]{2,119}$/.test(value)) {
		throw new Error("Harness Pi public config has an invalid Job ID");
	}
	return value;
}

function checkedSessionId(value: unknown): string {
	if (typeof value !== "string" || !/^[A-Za-z0-9_.:-]{1,180}$/.test(value)) {
		throw new Error("Harness Pi public config has an invalid session ID");
	}
	return value;
}

function decodeUtf8(data: Buffer, label: string): string {
	try {
		return new TextDecoder("utf-8", { fatal: true }).decode(data);
	} catch {
		throw new Error(`${label} is not valid UTF-8`);
	}
}

function assertWellFormedUnicode(value: string, label: string): void {
	for (let index = 0; index < value.length; index += 1) {
		const unit = value.charCodeAt(index);
		if (unit >= 0xd800 && unit <= 0xdbff) {
			const following = value.charCodeAt(index + 1);
			if (!(following >= 0xdc00 && following <= 0xdfff)) {
				throw new Error(`${label} contains an unpaired Unicode surrogate`);
			}
			index += 1;
		} else if (unit >= 0xdc00 && unit <= 0xdfff) {
			throw new Error(`${label} contains an unpaired Unicode surrogate`);
		}
	}
}

function canonicalJsonValue(
	value: unknown,
	ancestors: Set<object>,
	depth: number,
): unknown {
	if (depth > 64) throw new Error("Harness Pi RPC JSON exceeds its nesting cap");
	if (value === null || typeof value === "boolean") return value;
	if (typeof value === "string") {
		assertWellFormedUnicode(value, "Harness Pi RPC JSON string");
		return value;
	}
	if (typeof value === "number") {
		if (!Number.isFinite(value)) throw new Error("Harness Pi RPC JSON contains a non-finite number");
		return Object.is(value, -0) ? 0 : value;
	}
	if (typeof value !== "object") {
		throw new Error("Harness Pi RPC JSON contains a non-JSON value");
	}
	if (ancestors.has(value)) throw new Error("Harness Pi RPC JSON contains a cycle");
	ancestors.add(value);
	try {
		if (Array.isArray(value)) {
			const arrayKeys = Reflect.ownKeys(value);
			if (
				arrayKeys.length !== value.length + 1 ||
				!arrayKeys.includes("length") ||
				arrayKeys.some(
					(key) =>
						key !== "length" &&
						(typeof key !== "string" || !/^(?:0|[1-9][0-9]*)$/.test(key)),
				)
			) {
				throw new Error("Harness Pi RPC JSON contains a sparse or decorated array");
			}
			const normalized: unknown[] = [];
			for (let index = 0; index < value.length; index += 1) {
				const property = Object.getOwnPropertyDescriptor(value, String(index));
				if (!property?.enumerable || !("value" in property)) {
					throw new Error("Harness Pi RPC JSON contains a sparse or computed array entry");
				}
				normalized.push(canonicalJsonValue(property.value, ancestors, depth + 1));
			}
			return normalized;
		}
		const prototype = Object.getPrototypeOf(value);
		if (prototype !== Object.prototype && prototype !== null) {
			throw new Error("Harness Pi RPC JSON contains a non-plain object");
		}
		const ownKeys = Reflect.ownKeys(value);
		if (ownKeys.some((key) => typeof key !== "string")) {
			throw new Error("Harness Pi RPC JSON contains a symbolic key");
		}
		const normalized: Record<string, unknown> = Object.create(null);
		for (const key of (ownKeys as string[]).sort()) {
			assertWellFormedUnicode(key, "Harness Pi RPC JSON key");
			const property = Object.getOwnPropertyDescriptor(value, key);
			if (!property?.enumerable || !("value" in property)) {
				throw new Error("Harness Pi RPC JSON contains a hidden or computed property");
			}
			normalized[key] = canonicalJsonValue(property.value, ancestors, depth + 1);
		}
		return normalized;
	} finally {
		ancestors.delete(value);
	}
}

export function canonicalJsonBytes(value: unknown): Buffer {
	const normalized = canonicalJsonValue(value, new Set<object>(), 0);
	const serialized = JSON.stringify(normalized);
	if (serialized === undefined) throw new Error("Harness Pi RPC JSON is not serializable");
	return Buffer.from(serialized, "utf8");
}

export function encodeRpcFrame(value: unknown): Buffer {
	const payload = canonicalJsonBytes(value);
	if (payload.length < 1 || payload.length > MAX_RPC_REQUEST_BYTES) {
		throw new Error("Harness Pi RPC request exceeds its byte cap");
	}
	const frame = Buffer.allocUnsafe(4 + payload.length);
	frame.writeUInt32BE(payload.length, 0);
	payload.copy(frame, 4);
	return frame;
}

function readSealedRegularFile(path: string, label: string, maxBytes: number): Buffer {
	let descriptor: number | undefined;
	try {
		if (!isAbsolute(path) || resolve(path) !== path || realpathSync(path) !== path) {
			throw new Error(`${label} must have its fixed canonical absolute path`);
		}
		const lexicalMetadata = lstatSync(path);
		if (lexicalMetadata.isSymbolicLink() || !lexicalMetadata.isFile()) {
			throw new Error(`${label} must be a regular non-symlink file`);
		}
		if (lexicalMetadata.size > maxBytes) throw new Error(`${label} exceeds its byte cap`);
		descriptor = openSync(path, constants.O_RDONLY | constants.O_NOFOLLOW);
		const before = fstatSync(descriptor);
		if (!before.isFile() || before.size > maxBytes) {
			throw new Error(`${label} must be a bounded regular file`);
		}
		const data = readFileSync(descriptor);
		const after = fstatSync(descriptor);
		if (
			before.dev !== after.dev ||
			before.ino !== after.ino ||
			before.size !== after.size ||
			before.mtimeMs !== after.mtimeMs ||
			before.ctimeMs !== after.ctimeMs ||
			data.length !== after.size
		) {
			throw new Error(`${label} changed while it was read`);
		}
		return data;
	} finally {
		if (descriptor !== undefined) closeSync(descriptor);
	}
}

function parsePublicConfig(data: Buffer): PublicConfig {
	let parsed: unknown;
	try {
		parsed = JSON.parse(decodeUtf8(data, "Harness Pi public config"));
	} catch (error) {
		if (error instanceof Error && error.message.includes("not valid UTF-8")) throw error;
		throw new Error("Harness Pi public config is not valid JSON");
	}
	assertExactKeys(parsed, PUBLIC_CONFIG_KEYS, "Harness Pi public config");
	if (parsed.schema_version !== PUBLIC_CONFIG_SCHEMA) {
		throw new Error("Harness Pi public config schema mismatch");
	}

	const backend = parsed.backend;
	assertExactKeys(backend, BACKEND_KEYS, "Harness Pi backend");
	const sampling = backend.sampling;
	assertExactKeys(sampling, SAMPLING_KEYS, "Harness Pi backend sampling");
	const broker = parsed.broker;
	assertExactKeys(broker, BROKER_KEYS, "Harness Pi broker reference");
	if (broker.socket_env !== BROKER_SOCKET_ENV || broker.token_env !== BROKER_TOKEN_ENV) {
		throw new Error("Harness Pi broker environment references are not fixed");
	}
	if (parsed.system_prompt_path !== SEALED_SYSTEM_PROMPT_PATH) {
		throw new Error("Harness Pi system prompt path is not fixed");
	}
	if (parsed.settings_path !== SEALED_SETTINGS_PATH) {
		throw new Error("Harness Pi private settings path is not fixed");
	}

	return {
		schema_version: PUBLIC_CONFIG_SCHEMA,
		job_id: checkedJobId(parsed.job_id),
		session_id: checkedSessionId(parsed.session_id),
		backend: {
			kind: checkedString(backend.kind, "backend kind", 64),
			model: checkedString(backend.model, "backend model", 512),
			model_revision: checkedString(backend.model_revision, "backend model revision", 512),
			endpoint: checkedString(backend.endpoint, "backend endpoint", 4096),
			sampling: {
				max_tokens: sampling.max_tokens,
				temperature: sampling.temperature,
			},
		},
		extension_sha256: checkedHash(parsed.extension_sha256, "extension hash"),
		output_token_budget: positiveInteger(
			parsed.output_token_budget,
			"Harness Pi cumulative output-token budget",
		),
		prompt_sha256: checkedHash(parsed.prompt_sha256, "prompt hash"),
		prompt_size_bytes: positiveInteger(parsed.prompt_size_bytes, "prompt size"),
		system_prompt_path: SEALED_SYSTEM_PROMPT_PATH,
		system_prompt_sha256: checkedHash(parsed.system_prompt_sha256, "system prompt hash"),
		settings_path: SEALED_SETTINGS_PATH,
		settings_sha256: checkedHash(parsed.settings_sha256, "private settings hash"),
		broker: {
			socket_env: BROKER_SOCKET_ENV,
			token_env: BROKER_TOKEN_ENV,
		},
	};
}

function checkedSocketPath(raw: string): {
	path: string;
	device: number;
	inode: number;
} {
	if (!isAbsolute(raw) || resolve(raw) !== raw) {
		throw new Error("Harness Pi broker socket must have a canonical absolute path");
	}
	const metadata = lstatSync(raw);
	if (metadata.isSymbolicLink() || !metadata.isSocket() || realpathSync(raw) !== raw) {
		throw new Error("Harness Pi broker endpoint must be a canonical Unix socket");
	}
	return { path: raw, device: metadata.dev, inode: metadata.ino };
}

function checkedBrokerToken(raw: string): string {
	if (raw.length < 32 || raw.length > 256 || !/^[A-Za-z0-9_-]+$/.test(raw)) {
		throw new Error("Harness Pi broker token must be a bounded high-entropy token");
	}
	return raw;
}

function assertRuntimeIdentity(runtime: Runtime): void {
	const config = readSealedRegularFile(
		SEALED_PUBLIC_CONFIG_PATH,
		"Harness Pi public config",
		MAX_PUBLIC_CONFIG_BYTES,
	);
	if (sha256(config) !== runtime.configHash) {
		throw new Error("Harness Pi public config hash mismatch");
	}
	const extension = readSealedRegularFile(
		SEALED_EXTENSION_PATH,
		"Harness Pi extension",
		MAX_EXTENSION_BYTES,
	);
	if (sha256(extension) !== runtime.extensionHash) {
		throw new Error("Harness Pi extension hash mismatch");
	}
	const prompt = readSealedRegularFile(
		SEALED_SYSTEM_PROMPT_PATH,
		"Harness Pi system prompt",
		MAX_SYSTEM_PROMPT_BYTES,
	);
	if (sha256(prompt) !== runtime.systemPromptHash) {
		throw new Error("Harness Pi system prompt hash mismatch");
	}
	const settings = readSealedRegularFile(
		SEALED_SETTINGS_PATH,
		"Harness Pi private settings",
		MAX_SETTINGS_BYTES,
	);
	if (
		sha256(settings) !== runtime.settingsHash ||
		!settings.equals(PRIVATE_SETTINGS_BYTES)
	) {
		throw new Error("Harness Pi private settings identity mismatch");
	}
	if (requiredEnv("PI_CODING_AGENT_DIR") !== SEALED_AGENT_DIR) {
		throw new Error("Harness Pi private settings directory changed during the session");
	}
	if (requiredEnv(runtime.config.broker.token_env) !== runtime.token) {
		throw new Error("Harness Pi broker token changed during the session");
	}
	const socket = checkedSocketPath(requiredEnv(runtime.config.broker.socket_env));
	if (
		socket.path !== runtime.socketPath ||
		socket.device !== runtime.socketDevice ||
		socket.inode !== runtime.socketInode
	) {
		throw new Error("Harness Pi broker socket identity changed during the session");
	}
}

function loadRuntime(): Runtime {
	const configBytes = readSealedRegularFile(
		SEALED_PUBLIC_CONFIG_PATH,
		"Harness Pi public config",
		MAX_PUBLIC_CONFIG_BYTES,
	);
	const config = parsePublicConfig(configBytes);
	const loadedExtensionPath = fileURLToPath(import.meta.url);
	if (loadedExtensionPath !== SEALED_EXTENSION_PATH) {
		throw new Error("Harness Pi extension was not loaded from its fixed sealed path");
	}
	const extension = readSealedRegularFile(
		SEALED_EXTENSION_PATH,
		"Harness Pi extension",
		MAX_EXTENSION_BYTES,
	);
	if (sha256(extension) !== config.extension_sha256) {
		throw new Error("Harness Pi extension identity mismatch");
	}
	const prompt = readSealedRegularFile(
		SEALED_SYSTEM_PROMPT_PATH,
		"Harness Pi system prompt",
		MAX_SYSTEM_PROMPT_BYTES,
	);
	if (sha256(prompt) !== config.system_prompt_sha256) {
		throw new Error("Harness Pi system prompt identity mismatch");
	}
	const settings = readSealedRegularFile(
		SEALED_SETTINGS_PATH,
		"Harness Pi private settings",
		MAX_SETTINGS_BYTES,
	);
	if (
		sha256(settings) !== config.settings_sha256 ||
		!settings.equals(PRIVATE_SETTINGS_BYTES)
	) {
		throw new Error("Harness Pi private settings do not disable auto-compaction exactly");
	}
	if (requiredEnv("PI_CODING_AGENT_DIR") !== SEALED_AGENT_DIR) {
		throw new Error("Harness Pi private settings directory is not fixed");
	}
	const socket = checkedSocketPath(requiredEnv(config.broker.socket_env));
	const runtime: Runtime = {
		config,
		configHash: sha256(configBytes),
		extensionHash: config.extension_sha256,
		systemPromptHash: config.system_prompt_sha256,
		systemPrompt: decodeUtf8(prompt, "Harness Pi system prompt"),
		settingsHash: config.settings_sha256,
		socketPath: socket.path,
		socketDevice: socket.device,
		socketInode: socket.inode,
		token: checkedBrokerToken(requiredEnv(config.broker.token_env)),
	};
	assertRuntimeIdentity(runtime);
	return runtime;
}

function positiveInteger(value: unknown, label: string): number {
	if (typeof value !== "number" || !Number.isSafeInteger(value) || value < 1) {
		throw new Error(`${label} must be a positive integer`);
	}
	return value;
}

function finiteTemperature(value: unknown): number {
	if (typeof value !== "number" || !Number.isFinite(value) || value < 0 || value > 2) {
		throw new Error("temperature must be a finite number between 0 and 2");
	}
	return value;
}

function checkedEndpoint(raw: string): string {
	const endpoint = new URL(raw);
	if (
		!(endpoint.protocol === "http:" || endpoint.protocol === "https:") ||
		endpoint.username ||
		endpoint.password ||
		endpoint.search ||
		endpoint.hash
	) {
		throw new Error("Harness Leanstral endpoint must be credential-free HTTP(S)");
	}
	return raw.replace(/\/$/, "");
}

function reserveCall(toolCallId: string): number {
	if (typeof toolCallId !== "string" || !/^[A-Za-z0-9._:-]{1,180}$/.test(toolCallId)) {
		throw new Error("Harness Pi tool-call ID is malformed");
	}
	if (usedToolCallIds.has(toolCallId)) {
		throw new Error("Harness Pi tool-call ID was reused");
	}
	if (usedToolCallIds.size >= MAX_TRACKED_CALL_IDS) {
		throw new Error("Harness Pi tool-call ID budget was exhausted");
	}
	if (!Number.isSafeInteger(nextSequence) || nextSequence < 1) {
		throw new Error("Harness Pi RPC sequence was exhausted");
	}
	usedToolCallIds.add(toolCallId);
	const sequence = nextSequence;
	nextSequence += 1;
	return sequence;
}

function parseBrokerReply(
	runtime: Runtime,
	data: Buffer,
	sequence: number,
	toolCallId: string,
): BrokerReply {
	let reply: unknown;
	try {
		reply = JSON.parse(decodeUtf8(data, "Harness Pi broker response"));
	} catch (error) {
		if (error instanceof Error && error.message.includes("not valid UTF-8")) throw error;
		throw new Error("Harness Pi broker returned invalid JSON");
	}
	if (!isRecord(reply)) throw new Error("Harness Pi broker response must be an object");
	assertExactKeys(reply, RPC_RESPONSE_KEYS, "Harness Pi broker response");
	if (
		reply.protocol !== RPC_SCHEMA ||
		reply.job_id !== runtime.config.job_id ||
		reply.session_id !== runtime.config.session_id ||
		reply.sequence !== sequence ||
		reply.tool_call_id !== toolCallId
	) {
		throw new Error("Harness Pi broker response identity mismatch");
	}
	if (reply.ok === true) {
		if (reply.error !== null) {
			throw new Error("Harness Pi broker success response contains an error");
		}
		assertExactKeys(
			reply.result,
			isRecord(reply.result) && Object.prototype.hasOwnProperty.call(reply.result, "details")
				? RPC_RESULT_WITH_DETAILS_KEYS
				: RPC_RESULT_KEYS,
			"Harness Pi broker result",
		);
		if (typeof reply.result.text !== "string") {
			throw new Error("Harness Pi broker response text must be a string");
		}
		return {
			ok: true,
			text: reply.result.text,
			...(Object.prototype.hasOwnProperty.call(reply.result, "details")
				? { details: reply.result.details }
				: {}),
		};
	}
	if (reply.ok === false) {
		if (reply.result !== null || typeof reply.error !== "string" || reply.error.length < 1) {
			throw new Error("Harness Pi broker returned an invalid error");
		}
		throw new Error(`Harness Pi broker rejected the call: ${reply.error}`);
	}
	throw new Error("Harness Pi broker response has an invalid status");
}

function runBrokerRpc(
	runtime: Runtime,
	toolName: string,
	toolCallId: string,
	params: unknown,
	signal: AbortSignal | undefined,
): Promise<BrokerReply> {
	enforceInvariant(() => {
		if (!TOOL_SET.has(toolName)) throw new Error("Tool is not allowlisted");
		if (!isRecord(params)) throw new Error("Tool parameters must be an object");
		assertRuntimeIdentity(runtime);
	});

	const sequence = enforceInvariant(() => reserveCall(toolCallId));
	const request = {
		protocol: RPC_SCHEMA,
		job_id: runtime.config.job_id,
		session_id: runtime.config.session_id,
		sequence,
		tool_call_id: toolCallId,
		tool: toolName,
		token: runtime.token,
		params,
	};
	enforceInvariant(() => assertExactKeys(request, RPC_REQUEST_KEYS, "Harness Pi RPC request"));
	const frame = enforceInvariant(() => encodeRpcFrame(request));

	return new Promise((resolveReply, reject) => {
		const socket = createConnection({ path: runtime.socketPath });
		let settled = false;
		let received = Buffer.alloc(0);
		let expectedLength: number | undefined;
		let timer: ReturnType<typeof setTimeout> | undefined;

		const cleanup = () => {
			if (timer !== undefined) clearTimeout(timer);
			signal?.removeEventListener("abort", abort);
		};
		const fail = (error: Error) => {
			if (settled) return;
			settled = true;
			cleanup();
			socket.destroy();
			reject(error);
		};
		const succeed = (reply: BrokerReply) => {
			if (settled) return;
			settled = true;
			cleanup();
			socket.destroy();
			resolveReply(reply);
		};
		const abort = () => fail(new Error("Harness Pi broker RPC was aborted"));

		timer = setTimeout(
			() => fail(new Error("Harness Pi broker RPC exceeded its 30 second timeout")),
			RPC_TIMEOUT_MS,
		);
		if (signal?.aborted) {
			abort();
			return;
		}
		signal?.addEventListener("abort", abort, { once: true });

		socket.once("connect", () => {
			if (settled) return;
			try {
				socket.end(frame);
			} catch (error) {
				fail(error instanceof Error ? error : new Error(String(error)));
			}
		});
		socket.on("data", (chunk: Buffer) => {
			if (settled) return;
			if (received.length + chunk.length > MAX_RPC_RESPONSE_BYTES + 4) {
				fail(new Error("Harness Pi broker response exceeds its byte cap"));
				return;
			}
			received = Buffer.concat([received, chunk]);
			if (expectedLength === undefined && received.length >= 4) {
				expectedLength = received.readUInt32BE(0);
				if (expectedLength < 1 || expectedLength > MAX_RPC_RESPONSE_BYTES) {
					fail(new Error("Harness Pi broker returned an invalid frame length"));
					return;
				}
			}
			if (expectedLength === undefined) return;
			const framedLength = 4 + expectedLength;
			if (received.length > framedLength) {
				fail(new Error("Harness Pi broker returned trailing frame bytes"));
				return;
			}
			if (received.length === framedLength) {
				try {
					succeed(
						parseBrokerReply(runtime, received.subarray(4), sequence, toolCallId),
					);
				} catch (error) {
					fail(error instanceof Error ? error : new Error(String(error)));
				}
			}
		});
		socket.once("error", (error) => fail(error));
		socket.once("end", () => {
			if (!settled) fail(new Error("Harness Pi broker closed an incomplete response"));
		});
		socket.once("close", () => {
			if (!settled) fail(new Error("Harness Pi broker connection closed unexpectedly"));
		});
	});
}

function result(reply: BrokerReply) {
	return {
		content: [{ type: "text" as const, text: reply.text }],
		details: reply.details ?? {},
	};
}

function execute(
	runtime: Runtime,
	name: string,
	toolCallId: string,
	params: unknown,
	signal: AbortSignal | undefined,
) {
	return runBrokerRpc(runtime, name, toolCallId, params, signal).then(
		result,
		failClosedInvariant,
	);
}

function assertExactTools(pi: ExtensionAPI) {
	const active = [...pi.getActiveTools()].sort();
	const expected = [...TOOLS].sort();
	if (JSON.stringify(active) !== JSON.stringify(expected)) {
		throw new Error(`Harness Pi active-tool mismatch: ${active.join(",")}`);
	}
}

function assertProviderPromptAndTools(
	payload: Record<string, unknown>,
	runtime: Runtime,
): void {
	if (!Array.isArray(payload.messages)) {
		throw new Error("Harness Pi provider payload has no message list");
	}
	if (payload.model !== runtime.config.backend.model || payload.stream !== true) {
		throw new Error("Harness Pi provider payload changed the pinned model or stream mode");
	}
	if (
		!isRecord(payload.stream_options) ||
		payload.stream_options.include_usage !== true
	) {
		throw new Error("Harness Pi provider payload disabled streaming usage");
	}
	const systemMessages = payload.messages.filter(
		(message) => isRecord(message) && message.role === "system",
	);
	if (
		systemMessages.length !== 1 ||
		!isRecord(systemMessages[0]) ||
		systemMessages[0].content !== runtime.systemPrompt
	) {
		throw new Error("Harness Pi provider payload changed the sealed system prompt");
	}
	const userMessages = payload.messages.filter(
		(message) => isRecord(message) && message.role === "user",
	);
	if (userMessages.length !== 1 || !isRecord(userMessages[0])) {
		throw new Error("Harness Pi provider payload changed the exact user-message count");
	}
	const userContent = userMessages[0].content;
	if (
		!Array.isArray(userContent) ||
		userContent.length !== 1 ||
		!isRecord(userContent[0]) ||
		userContent[0].type !== "text"
	) {
		throw new Error("Harness Pi provider payload changed the user-message encoding");
	}
	assertPromptIdentity(
		userContent[0].text,
		runtime.config.prompt_sha256,
		runtime.config.prompt_size_bytes,
	);
	if (!Array.isArray(payload.tools) || payload.tools.length !== TOOLS.length) {
		throw new Error("Harness Pi provider payload changed the exact tool set");
	}
	const names = payload.tools.map((tool) => {
		if (!isRecord(tool) || tool.type !== "function" || !isRecord(tool.function)) {
			throw new Error("Harness Pi provider payload contains a malformed tool");
		}
		return tool.function.name;
	});
	if (
		names.some((name) => typeof name !== "string") ||
		JSON.stringify([...names].sort()) !== JSON.stringify([...TOOLS].sort())
	) {
		throw new Error("Harness Pi provider payload changed the exact tool names");
	}
}

function installHarnessPiExtension(pi: ExtensionAPI) {
	const runtime = loadRuntime();
	const backend = runtime.config.backend;
	if (backend.kind !== "leanstral" || !backend.model || !backend.model_revision) {
		throw new Error("Harness Pi requires a pinned Leanstral backend");
	}
	const baseUrl = checkedEndpoint(backend.endpoint);
	const maxTokens = positiveInteger(backend.sampling.max_tokens, "max_tokens");
	const outputBudget = positiveInteger(
		runtime.config.output_token_budget,
		"output_token_budget",
	);
	const budget = new HarnessOutputBudget(maxTokens, outputBudget);
	const temperature = finiteTemperature(backend.sampling.temperature);
	let beforeAgentStartCount = 0;

	pi.registerProvider(PROVIDER, {
		name: "Harness Leanstral",
		baseUrl,
		apiKey: "unused",
		authHeader: false,
		api: "openai-completions",
		models: [
			{
				id: backend.model,
				name: `${backend.model} (${backend.model_revision.slice(0, 12)})`,
				reasoning: false,
				input: ["text"],
				cost: { input: 0, output: 0, cacheRead: 0, cacheWrite: 0 },
				contextWindow: CONTEXT_WINDOW,
				maxTokens,
				compat: {
					supportsStore: false,
					supportsDeveloperRole: false,
					supportsReasoningEffort: false,
					supportsUsageInStreaming: true,
					supportsStrictMode: false,
					maxTokensField: "max_tokens",
					requiresToolResultName: true,
				},
			},
		],
	});

	pi.registerTool({
		name: "read_context",
		label: "Read Task context",
		description: "Read a bounded line range from an immutable Task context file or exact allowed file.",
		parameters: Type.Object(
			{
				path: Type.String({ maxLength: 1024 }),
				start_line: Type.Optional(Type.Integer({ minimum: 1 })),
				max_lines: Type.Optional(Type.Integer({ minimum: 1, maximum: 400 })),
			},
			{ additionalProperties: false },
		),
		executionMode: "sequential",
		async execute(id, params, signal) {
			return execute(runtime, "read_context", id, params, signal);
		},
	});

	pi.registerTool({
		name: "search_symbol",
		label: "Search Task symbols",
		description: "Search for a literal symbol only within bounded Task-readable files.",
		parameters: Type.Object(
			{
				symbol: Type.String({ minLength: 1, maxLength: 256 }),
				paths: Type.Optional(Type.Array(Type.String({ maxLength: 1024 }), { maxItems: 64 })),
				max_results: Type.Optional(Type.Integer({ minimum: 1, maximum: 200 })),
			},
			{ additionalProperties: false },
		),
		executionMode: "sequential",
		async execute(id, params, signal) {
			return execute(runtime, "search_symbol", id, params, signal);
		},
	});

	pi.registerTool({
		name: "apply_patch_scoped",
		label: "Apply scoped patch",
		description: "Apply one unified diff only to existing files allowed by the immutable Task scope.",
		parameters: Type.Object(
			{ patch: Type.String({ minLength: 1, maxLength: 524_288 }) },
			{ additionalProperties: false },
		),
		executionMode: "sequential",
		async execute(id, params, signal) {
			return execute(runtime, "apply_patch_scoped", id, params, signal);
		},
	});

	pi.registerTool({
		name: "lean_check",
		label: "Run allowlisted Lean check",
		description: "Run one zero-based Task acceptance entry, only when it is an explicitly supported Lean/lake argv.",
		parameters: Type.Object(
			{ command_index: Type.Integer({ minimum: 0 }) },
			{ additionalProperties: false },
		),
		executionMode: "sequential",
		async execute(id, params, signal) {
			return execute(runtime, "lean_check", id, params, signal);
		},
	});

	pi.registerTool({
		name: "git_diff",
		label: "Inspect diff",
		description: "Inspect the scoped checkout through fixed read-only git status/diff invocations.",
		parameters: Type.Object(
			{
				view: Type.Optional(
					Type.Union([
						Type.Literal("patch"),
						Type.Literal("check"),
						Type.Literal("name_only"),
						Type.Literal("stat"),
						Type.Literal("status"),
					]),
				),
			},
			{ additionalProperties: false },
		),
		executionMode: "sequential",
		async execute(id, params, signal) {
			return execute(runtime, "git_diff", id, params, signal);
		},
	});

	pi.registerTool({
		name: "report_blocked",
		label: "Report exact blocker",
		description: "Record an exact structured blocker without changing Harness Task or Job state.",
		parameters: Type.Object(
			{
				summary: Type.String({ minLength: 1, maxLength: 16_384 }),
				exact_lean_type_or_error: Type.String({ minLength: 1, maxLength: 65_536 }),
				attempted_routes: Type.Array(Type.String({ minLength: 1, maxLength: 8192 }), {
					minItems: 1,
					maxItems: 32,
				}),
				strongest_partial_result: Type.String({ minLength: 1, maxLength: 32_768 }),
			},
			{ additionalProperties: false },
		),
		executionMode: "sequential",
		async execute(id, params, signal) {
			const reply = await execute(runtime, "report_blocked", id, params, signal);
			return { ...reply, terminate: true } as typeof reply & { terminate: true };
		},
	});

	pi.on("session_start", () => {
		enforceInvariant(() => {
			pi.setActiveTools([...TOOLS]);
			assertExactTools(pi);
			assertRuntimeIdentity(runtime);
		});
	});

	pi.on("before_agent_start", (event) => {
		return enforceInvariant(() => {
			assertExactTools(pi);
			assertRuntimeIdentity(runtime);
			if (beforeAgentStartCount !== 0) {
				throw new Error("Harness Pi received more than one Job prompt");
			}
			beforeAgentStartCount += 1;
			if (event.images?.length) {
				throw new Error("Harness Pi rejected images in the canonical Job prompt");
			}
			assertPromptIdentity(
				event.prompt,
				runtime.config.prompt_sha256,
				runtime.config.prompt_size_bytes,
			);
			if (
				event.systemPromptOptions.contextFiles?.length ||
				event.systemPromptOptions.skills?.length
			) {
				throw new Error("Harness Pi rejected ambient context files or skills");
			}
			if (event.systemPromptOptions.customPrompt !== runtime.systemPrompt) {
				throw new Error("Harness Pi system prompt did not come from its sealed file");
			}
			return { systemPrompt: runtime.systemPrompt };
		});
	});

	pi.on("session_before_compact", () => {
		enforceInvariant(() => {
			throw new Error("Harness Pi rejected a forbidden compaction attempt");
		});
	});

	pi.on("session_compact", () => {
		enforceInvariant(() => {
			throw new Error("Harness Pi rejected a completed compaction path");
		});
	});

	pi.on("message_start", (event) => {
		enforceInvariant(() => {
			if (event.message.role !== "assistant") return;
			assertExactTools(pi);
			assertRuntimeIdentity(runtime);
			budget.observe(event.message);
		});
	});

	pi.on("message_update", (event) => {
		enforceInvariant(() => {
			if (event.message.role !== "assistant") return;
			assertExactTools(pi);
			assertRuntimeIdentity(runtime);
			budget.observe(event.message);
		});
	});

	pi.on("message_end", (event) => {
		enforceInvariant(() => {
			assertExactTools(pi);
			assertRuntimeIdentity(runtime);
			if (event.message.role !== "assistant") return;
			budget.complete(event.message);
			const toolCalls = event.message.content.filter((part) => part.type === "toolCall");
			if (
				toolCalls.some((call) => call.name === "report_blocked") &&
				toolCalls.length !== 1
			) {
				throw new Error("Harness Pi requires report_blocked to be the only call in its turn");
			}
		});
	});

	pi.on("agent_settled", () => {
		enforceInvariant(() => {
			assertExactTools(pi);
			assertRuntimeIdentity(runtime);
			if (beforeAgentStartCount !== 1) {
				throw new Error("Harness Pi settled without exactly one canonical Job prompt");
			}
			budget.assertSettled();
		});
	});

	pi.on("tool_call", (event) => {
		enforceInvariant(() => {
			assertExactTools(pi);
			assertRuntimeIdentity(runtime);
			if (!TOOL_SET.has(event.toolName)) {
				throw new Error(`Tool is outside the exact Harness Pi allowlist: ${event.toolName}`);
			}
		});
	});

	pi.on("before_provider_request", (event) => {
		return enforceInvariant(() => {
			assertExactTools(pi);
			assertRuntimeIdentity(runtime);
			if (beforeAgentStartCount !== 1) {
				throw new Error("Harness Pi provider request escaped the canonical Job prompt");
			}
			if (!isRecord(event.payload)) {
				throw new Error("Harness Pi rejected a non-object provider payload");
			}
			const payload = { ...event.payload };
			assertProviderPromptAndTools(payload, runtime);
			payload.temperature = temperature;
			payload.max_tokens = budget.beginRequest(payload.max_tokens);
			for (const unsupported of [
				"frequency_penalty",
				"max_completion_tokens",
				"min_p",
				"presence_penalty",
				"reasoning_effort",
				"seed",
				"top_k",
				"top_p",
			]) {
				delete payload[unsupported];
			}
			return payload;
		});
	});
}

export default function harnessPiExtension(pi: ExtensionAPI) {
	enforceInvariant(() => installHarnessPiExtension(pi));
}
