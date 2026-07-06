# M2-scope-1 assets: short-time existence scoping

## Pinned Mathlib inventory

Toolchain: `leanprover/lean4:v4.30.0-rc2`.  Mathlib is pinned in
`lake-manifest.json` to `7175569c842f9164564bd76ff8b207e7b4705522`.

| Ingredient | Verdict | Local evidence | Short-time-existence impact |
|---|---:|---|---|
| Sobolev spaces | partial | `.lake/packages/mathlib/Mathlib/Analysis/Distribution/Sobolev.lean` defines Bessel-potential `TemperedDistribution.memSobolev`; `.lake/packages/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean` proves Gagliardo-Nirenberg-Sobolev estimates. | Useful Euclidean/Fourier foundations, but no closed-manifold tensor Sobolev scale or parabolic bootstrapping API. |
| Holder spaces | partial | `.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Holder.lean` and `HolderNorm.lean` define `HolderWith`, `MemHolder`, `eHolderNorm`, `nnHolderNorm`. | Metric Holder continuity exists, but not the classical `C^{k,alpha}` or parabolic `C^{2+alpha,1+alpha/2}` Banach spaces needed for Schauder theory. |
| Heat semigroup/kernel | absent | No `Mathlib/Analysis/*Heat*`, `*Parabolic*`, or heat-kernel modules in the pinned tree; repo has model-level heat predicates in `Poincare/ModelLaplacian.lean`. | The heat-kernel/semigroup route would need new statement and analysis layers. |
| Linear parabolic existence / Schauder | absent | No pinned Mathlib `Parabolic` or `Schauder` modules. Existing repo names such as `ParabolicLinearTheoryData` and `ParabolicSchauderEstimateData` are project interfaces, not Mathlib theorems. | This is the main analytic gap behind Hamilton-DeTurck short-time existence. |
| Second-order elliptic operators | partial | Mathlib has distributional `laplacian` facts in `Analysis/Distribution/Sobolev.lean`; the repo has closed-metric `laplacianAt` in `Poincare/Global/Laplacian.lean`. | Laplacian vocabulary exists, but not a general strongly elliptic operator/Schauder/resolvent library. |
| Function-space completeness tools | exists | `MeasureTheory/Function/LpSpace/Complete.lean`, `Analysis/Normed/Lp/SmoothApprox.lean`, `Analysis/Calculus/BumpFunction/*`, and `Analysis/Fourier/*`. | Good raw material for Banach fixed points and approximation, but still below a parabolic PDE library. |
| ODE in Banach spaces | exists | `Mathlib/Analysis/ODE/PicardLindelof.lean`, plus `Basic.lean`, `Gronwall.lean`, `Transform.lean`. | Strong fit for DeTurck diffeomorphism ODEs after the vector field is expressed in a Banach/smooth setting. |

## Hamilton-DeTurck obligation map

The front-A short-time-existence wall decomposes into these repo-vocabulary
obligations.  Difficulty is relative to current assets.

| Obligation | Repo vocabulary | Difficulty | Notes |
|---|---|---:|---|
| Public closed-flow interface | `RicciFlowShortTimeExistence3`, `ClosedSmoothRiemannianMetric 3 M`, `IsClosedRicciFlowSolutionAt` | S, done here | Statement layer only; no PDE proof claimed. |
| Static/non-vacuity sanity | `isClosedRicciFlowSolutionAt_const_of_ricciFlat`, `ClosedC2TangentField`, `static_ricciFlat_flowClause` | S, done here | Shows the flow clause is satisfiable in the Ricci-flat static case, not generally. |
| DeTurck gauge data | `HasDeTurckGaugeFixing`, `HasDeTurckBackgroundMetricCompatibility`, `DeTurckVectorFieldConstructionData`, `HasDeTurckVectorFieldConstruction` | M | Needs a closed-metric version of the connection-difference trace vector field. |
| Ricci-DeTurck PDE statement | `RicciDeTurckEquationDerivationData`, `HasDeTurckEquationDerivation`, `RicciDeTurckLinearizationData`, `HasRicciDeTurckLinearization` | L | Mostly tensor-calculus statement engineering before proof of analytic estimates. |
| Strict parabolicity | `StrictlyParabolicDeTurckSystemData`, `HasStrictlyParabolicDeTurckSystem` | L | Principal-symbol computation for symmetric 2-tensors after DeTurck gauge fixing. |
| Parabolic theory and fixed point | `ParabolicLinearTheoryData`, `HasParabolicLinearTheory`, `ParabolicFixedPointArgumentData`, `HasParabolicFixedPointArgument`, `HasDeTurckShortTimeExistence` | XL | Pinned Mathlib lacks the required parabolic existence/Schauder layer. |
| Pullback back to Ricci flow | `DeTurckDiffeomorphismODEData`, `HasDeTurckDiffeomorphismODE`, `DeTurckPullbackEquationIdentityData`, `HasDeTurckPullbackEquationIdentity`, `HasDeTurckPullbackToRicciFlow` | L | Banach ODE tools exist; geometric pullback identity must be stated and connected. |
| Evolution-layer regularity bridge | `ClosedRicciFlowExtensionRegularAt`, `MetricFlowRegularAt`, `TimeDifferentiableAt`, `HamiltonScalarEvolutionPredicatesAt`, `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow` | M/L | Short-time existence gives the flow clause, but scalar evolution still needs regularity/assembly predicates. |

The repo already has the Hamilton pinching estimates proved as
`hamilton_pinching_preserved` and `hamilton_pinching_improvement`; those belong
to front B.  The convergence target for front C remains
`PositiveEinsteinMetric3` and `HamiltonConvergencePinchedLimit3Core`.

## New statement layer

New file: `Poincare/Global/ShortTimeInterface.lean`.  Existing files,
including `Poincare.lean`, were not edited.

Final declarations:

```lean
def RicciFlowShortTimeExistence3 (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop
```

Payload: for every `g₀ : ClosedSmoothRiemannianMetric 3 M`, there exist
`T > 0` and `gt : ℝ → ClosedSmoothRiemannianMetric 3 M` with `gt 0 = g₀`
and `∀ t ∈ Set.Ico 0 T, ∀ x : M, IsClosedRicciFlowSolutionAt gt t x`.

```lean
@[reducible] def shortTimeMetricFamilyInhabited
    (g₀ : ClosedSmoothRiemannianMetric 3 M) :
    Inhabited (ℝ → ClosedSmoothRiemannianMetric 3 M)

theorem const_metricFamily_zero
    (g₀ : ClosedSmoothRiemannianMetric 3 M) :
    (fun _ : ℝ ↦ g₀) 0 = g₀

theorem static_ricciFlat_flowClause
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hric : ∀ x : M, ∀ {Z : ∀ y : M, TM y},
      ClosedC2TangentField (n := 3) (M := M) Z →
        ∀ (hreg : CovariantDerivative.DerivRegularAt g.leviCivita Z x)
          (w : TM x),
          CovariantDerivative.ricciTraceAt g.leviCivita hreg w = 0)
    (T : ℝ) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
      IsClosedRicciFlowSolutionAt (fun _ : ℝ ↦ g) t x

theorem exists_shortTime_ricciFlow_of_interface
    (hShort : RicciFlowShortTimeExistence3 M)
    (g₀ : ClosedSmoothRiemannianMetric 3 M) :
    ∃ T : ℝ, 0 < T ∧
      ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
        gt 0 = g₀ ∧
          ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
            IsClosedRicciFlowSolutionAt gt t x

theorem exists_shortTime_flow_half_of_hamiltonScalarEvolution_input
    (hShort : RicciFlowShortTimeExistence3 M)
    (g₀ : ClosedSmoothRiemannianMetric 3 M) :
    ∃ T : ℝ, ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
      0 < T ∧ gt 0 = g₀ ∧
        ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
          IsClosedRicciFlowSolutionAt gt t x ∧
            (∀ᶠ y in nhds x, IsClosedRicciFlowSolutionAt gt t y)

theorem eventually_isClosedRicciFlowSolutionAt_of_shortTime_flow
    {T : ℝ} {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    (hflow : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
      IsClosedRicciFlowSolutionAt gt t x)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) T) (x : M) :
    ∀ᶠ y in nhds x, IsClosedRicciFlowSolutionAt gt t y
```

Consumption boundary: `exists_shortTime_flow_half_of_hamiltonScalarEvolution_input`
extracts the flow clause and the flow-only neighborhood clause used inside the
`satisfiesHamiltonScalarEvolutionAt_of_ricciFlow` family.  It deliberately does
not derive `ClosedRicciFlowExtensionRegularAt`, `MetricFlowRegularAt`,
`TimeDifferentiableAt`, metric-raise differentiability, or
`HamiltonScalarEvolutionPredicatesAt`.

## DeTurck statement-layer roadmap

1. Add a closed-metric `DeTurckVectorField3` statement interface using
   `ClosedSmoothRiemannianMetric 3 M`, `(gt t).leviCivita`, and a fixed
   background metric, then connect it to `DeTurckVectorFieldConstructionData`.
2. State `RicciDeTurckFlowSolutionAt3` and a `RicciDeTurckShortTimeExistence3`
   interface whose payload is a positive-time family satisfying the
   Ricci-DeTurck PDE, with `StrictlyParabolicDeTurckSystemData`,
   `ParabolicLinearTheoryData`, and `ParabolicFixedPointArgumentData` left as
   explicit analytic inputs.
3. State the diffeomorphism ODE layer using `DeTurckDiffeomorphismODEData` and
   Mathlib `IsPicardLindelof`; prove only shape lemmas until the vector-field
   regularity hypotheses are available.
4. State and prove a conditional pullback theorem:
   `DeTurckPullbackEquationIdentityData` plus `HasDeTurckDiffeomorphismODE`
   yields a family satisfying `IsClosedRicciFlowSolutionAt`.
5. Add the regularity bridge from the smooth DeTurck-produced family to
   `ClosedRicciFlowExtensionRegularAt` and `HamiltonScalarEvolutionPredicatesAt`
   so the short-time layer can feed the existing scalar-evolution theorems.

## Verification

Required command run:

```text
lake build Poincare.Global.ShortTimeInterface
```

Actual result: success, `Build completed successfully (3076 jobs)`.  The build
replayed existing modules with non-blocking warnings and `#check` info from
`Poincare.Global.Statement`; no forbidden proof placeholders or unsafe native
decision hooks were introduced.
