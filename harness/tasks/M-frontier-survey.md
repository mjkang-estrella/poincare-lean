Read harness/worker_contract.md first and obey it strictly.

# Task M-frontier-survey: scope the two remaining walls — choose goal 7

Six goals are gate-verified (Levi-Civita foundation; Hamilton scalar + Ricci evolution equations; singularity/positivity suite; pinching preservation; pinching improvement — read HARNESS_STATUS.md and harness/reports/M4-audit-5_done.md for the current honest ceiling). Two major walls remain before Hamilton 1982 is complete, plus the M2 wall. This is a SURVEY task (read + report; no proof obligations):

For each candidate front, inventory: what the repo already provides, what Mathlib provides, the 3-6 keystone lemmas, the honest difficulty, and a 5-10 task opening roadmap:

**A. Hamilton §11-17 convergence chain**: gradient estimate for R (the |∇R|² interpolation, needs higher-derivative Bochner), the eigenvalue-pinching → diameter/injectivity control, normalized-flow convergence to constant curvature. Which pieces are estimate-algebra (our proven strength) vs genuinely new analysis (Sobolev/interpolation — check Mathlib's status on manifold Sobolev spaces, integration on manifolds — likely THE wall)?

**B. M2 short-time existence**: DeTurck trick reduction, parabolic systems on manifolds — check Mathlib's parabolic PDE status (almost certainly absent; the wall would be building linear parabolic existence from scratch). What is the MINIMAL honest interface (a well-posedness Prop + its consequences) vs the full construction?

**C. (dark horse) Sphere-recognition endgame**: given the proven pinching improvement, what remains to state+prove "pinched limit ⟹ constant sectional curvature ⟹ (by existing space-form theory?) round"? Check Mathlib for space-form classification / constant-curvature rigidity.

Recommend ONE front with justification (tractability × value toward the Poincaré statement chain). Report to harness/reports/M-frontier-survey.md. Standing protocols; no Lean changes required.
