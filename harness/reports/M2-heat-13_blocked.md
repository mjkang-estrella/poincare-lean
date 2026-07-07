Blocked: `Poincare/Global/HeatCauchyUniform.lean` verifies the requested
uniform closed-ball translate envelope layer, but the full spatial Frechet
interchange and unconditional model Cauchy theorem are still blocked by missing
second/third operator-valued derivative estimates.

Verified payload in the new module:

* `heatKernelUniformTranslateEnvelope` is a fixed integrable envelope in `y`
  with widened Gaussian `exp (-(1 / (16 * t)) * ‖y‖ ^ 2)`.
* `integrable_heatKernelUniformTranslateEnvelope` proves integrability for
  every positive `t`.
* `heatKernel_translate_polynomial_le_uniformEnvelope` proves the uniform
  translate estimate for `x ∈ closedBall x₀ R`, `0 ≤ R`, and every polynomial
  order `m ≤ 3`.
* `heatKernel_translate_order_one_le_uniformEnvelope`,
  `heatKernel_translate_order_two_le_uniformEnvelope`, and
  `heatKernel_translate_order_three_le_uniformEnvelope` expose the requested
  order `1`, `2`, and `3` instances.
* `fderiv_heatKernel_norm_le_uniformTranslateEnvelope` proves the first
  spatial Frechet derivative operator norm is dominated by the order-one
  uniform envelope.

Remaining blocker:

* The inspected heat files provide the kernel PDE, the time interchange, and a
  first Frechet operator estimate, but not the corresponding second and third
  Frechet operator-norm formulas/estimates needed to run the two spatial
  `hasFDerivAt_integral_of_dominated_loc_of_lip` applications honestly.
* Because those operator-valued next-order bounds are not yet available, the
  spatial Laplacian interchange and the unconditional model Cauchy theorem were
  not claimed.

Verification:

* `lake build Poincare.Global.HeatCauchyUniform` completed successfully:
  `Build completed successfully (2749 jobs).`
