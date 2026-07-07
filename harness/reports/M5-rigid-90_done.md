# M5-rigid-90 done: a-priori Gronwall membership, no pinned circularity

## Status

Added `Poincare/Global/GronwallMembership.lean`.  No existing Lean files were
edited, including `Poincare.lean`.

The new module proves the non-circular membership layer:

- `GronwallMembership.linearODE_norm_le_exp_of_opNorm_le`
- `GronwallMembership.linearODE_norm_le_exp_T_of_opNorm_le`
- `GronwallMembership.linearODE_mem_closedBall_zero_of_opNorm_le`
- `GronwallMembership.linearODE_mem_closedBall_initial_of_opNorm_le`
- `GronwallMembership.linearODE_mem_closedBall_initial_of_radius_ge`

It then connects the actual corrected Jacobi norm triple to the speed-generic
linear norm ODE without invoking the pinned-value theorem:

- `GronwallMembership.correctedD`
- `GronwallMembership.normState`
- `GronwallMembership.normState_hasDerivAt_speed`
- `GronwallMembership.normState_hasDerivWithinAt_speed_on_Icc`
- `GronwallMembership.normState_continuousOn_Icc`

The final membership forms are the feed-shaped facts:

- `GronwallMembership.normState_mem_closedBall_zero_of_opNorm_le`
- `GronwallMembership.normState_mem_closedBall_initial_of_opNorm_le`
- `GronwallMembership.normState_mem_closedBall_qcenter_of_opNorm_le`
- `GronwallMembership.normState_mem_closedBall_qcenter_of_radius_ge`

The bounded-direction handoff is recorded as:

- `GronwallMembership.norm_triple_zero_zero`
- `GronwallMembership.qcenter_gronwall_radius_le_of_abs_le`

Thus a bound `|q(w)| <= qmax` on a bounded `w`-ball can be composed with the
fixed-radius theorem to produce one closed-ball radius; the proof path does not
use `actual_jacobi_norms_eq_speed_pinned_on_cutoff_one_Icc`.

## Verification

- `lake build Poincare.Global.GronwallMembership`
  - Result: success.
  - Final lines:

```text
✔ [3180/3180] Built Poincare.Global.GronwallMembership (3.4s)
Build completed successfully (3180 jobs).
```

- `rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/GronwallMembership.lean`
  - Result: no matches.

- `git diff --check -- Poincare/Global/GronwallMembership.lean`
  - Result: success.
