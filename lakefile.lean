import Lake
open Lake DSL

package «poincare» where
  -- This project is a scaffold. It is not a completed formal proof.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib Poincare where
  roots := #[`Poincare]
