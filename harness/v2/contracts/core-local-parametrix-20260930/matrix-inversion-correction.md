# Explicit coefficient inversion correction

The original local-family attempt is preserved at base
`127725fb499b88b5b35654479d8859afeb8f4448`. Its first compiler failure
showed that bare inverse notation inside chartValue's function-valued expected
type elaborated `@Inv.inv (Fin 3 -> Fin 3 -> Real) Pi.instInv`. The actual
proved single-chart solver returns coefficients elaborated with
`@Inv.inv (Matrix (Fin 3) (Fin 3) Real) Matrix.inv`. These operations are
different. Changing an open namespace to make a mismatched statement appear
to compile would not be acceptable frozen-contract verification.

The original Task, independent readback, failed source, exact compiler output
and blocked report remain intact. A superseding reviewed Task makes Matrix.inv
explicit in the output residual. All input hypotheses, support restrictions,
common-time quantifiers, norm bounds and the plus-residual sign are unchanged.
This correction repairs an unaccepted draft's intended coefficient operation;
it does not alter the final Poincare target or add an existence premise.

Core assumption helped: UniversalHamiltonConvergenceStatement. Subsequent
consumer: construction of global bounded tensor L/P/R for actual DeTurck
evolution. The local-family proof constructs its atlas, buffers and operators
from g0 and alpha rather than accepting them. The actual physical flow,
ordinary joint C3 at time zero, global continuation/surgery and favorable
metric/limit production remain open, as does smoothability.
