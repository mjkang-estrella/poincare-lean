#!/usr/bin/env python3
"""Report proof placeholders in Lean sources, ignoring comments and docstrings.

Prints one ``path:line:text`` per hit, sorted, for lines whose code (after
removing ``--`` line comments and ``/- ... -/`` block comments, including nested
and documentation comments) declares ``opaque``, ``axiom``, ``postulate``, or a
Lean 3 style ``constant``, or mentions ``sorry`` or ``admit`` as a word. Comment
text is not a placeholder; Lean itself reports ``sorryAx`` in axiom footprints.
Exit status is 0 whether or not hits are found; callers test the output.
"""

from __future__ import annotations

import os
import re
import sys

DECLARATION = re.compile(r"^\s*(opaque|axiom|postulate)\s+")
CONSTANT = re.compile(r"^\s*constant\s+[A-Za-z_][A-Za-z0-9_]*(\s*:|\s+.*:|\s*$)")
WORD = re.compile(r"\b(sorry|admit)\b")


def strip_comments(text: str) -> str:
    """Blank out comments while preserving line structure."""
    out = []
    i = 0
    depth = 0
    length = len(text)
    while i < length:
        ch = text[i]
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            out.append("  ")
            i += 2
            continue
        if text.startswith("--", i):
            end = text.find("\n", i)
            end = length if end < 0 else end
            out.append(" " * (end - i))
            i = end
            continue
        if ch == '"':
            end = i + 1
            while end < length and text[end] != '"':
                end += 2 if text[end] == "\\" else 1
            end = min(end + 1, length)
            out.append(" " * (end - i))
            i = end
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def lean_files(paths):
    for path in paths:
        if os.path.isdir(path):
            for directory, subdirectories, filenames in os.walk(path):
                subdirectories[:] = sorted(d for d in subdirectories if not d.startswith("."))
                for name in sorted(filenames):
                    if name.endswith(".lean"):
                        yield os.path.join(directory, name)
        elif path.endswith(".lean"):
            yield path


def scan(paths):
    hits = []
    for path in lean_files(paths):
        with open(path, encoding="utf-8", errors="surrogateescape") as handle:
            original = handle.read()
        code = strip_comments(original)
        original_lines = original.split("\n")
        for number, line in enumerate(code.split("\n"), 1):
            if DECLARATION.search(line) or CONSTANT.search(line) or WORD.search(line):
                hits.append(f"{path}:{number}:{original_lines[number - 1]}")
    return sorted(set(hits))


if __name__ == "__main__":
    for hit in scan(sys.argv[1:] or ["."]):
        print(hit)
