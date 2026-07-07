Blocked: the new module `Poincare/Global/HeatCauchyFrechet.lean` verifies one
strict Frechet-specific estimate, but the full twice-Frechet dominated
differentiation route is still missing the required spatially local
operator-valued domination layer.

Verified payload:

* `heatKernelSpatialFDerivIntegrand` defines the operator-valued first spatial
  Frechet derivative integrand for `x ↦ heatKernel t (x - y) * c`.
* `heatKernel_spatial_fderiv_integrand_norm_le_firstSpatialEnvelope` proves
  its operator norm is dominated by the existing Gaussian-polynomial envelope
  `heatKernelFirstSpatialEnvelope`.

Why the full theorem is still blocked:

* Mathlib's
  `hasFDerivAt_integral_of_dominated_loc_of_lip` needs an a.e. Lipschitz bound
  on a neighborhood of the spatial base point, or equivalently via
  `hasFDerivAt_integral_of_dominated_of_fderiv_le`, a bound
  `∀ x ∈ s, ‖F' x y‖ ≤ bound y` with `s ∈ 𝓝 x₀`.
* The current heat files provide fixed-center scalar envelopes.  They do not
  yet provide a uniform-in-`x ∈ s` Gaussian translate envelope for the
  operator-valued first derivative, nor the analogous second/third Frechet
  operator envelopes needed to run the second differentiation into
  `E →L[ℝ] ℝ`.
* Without that local operator-valued Lipschitz/envelope layer, the first
  Frechet interchange cannot be honestly applied, so the second interchange,
  Laplacian identification, and unconditional model Cauchy theorem cannot be
  closed without adding an unsupported hypothesis.

Verification:

* `lake build Poincare.Global.HeatCauchyFrechet` completed successfully:
  `Build completed successfully (2748 jobs).`
