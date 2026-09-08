import Lake
open Lake DSL

package «poincare» where
  -- This project is a scaffold. It is not a completed formal proof.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib Poincare where
  roots := #[`Poincare]

-- Checked-in audit payloads (formerly shell heredocs). Not a default target:
-- `lake build` is unchanged; `lake build PoincareAudit` elaborates the audit surface
-- and Lake caches the result. See scripts/audit_payload_equivalence.py.
lean_lib PoincareAudit where
  srcDir := "audit"
  roots := #[`PoincareAudit]
