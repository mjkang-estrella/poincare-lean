import Poincare.Global.ProofBearingEndToEndCompletion
import Poincare.Global.CartanAtlasAutomaticAnchorAlignment

/-!
# End-to-end conditional route with a constant Cartan target

This module records the strong constant-north-pole specialization from
`CartanAtlasAutomaticAnchorAlignment`.  Tangent alignments are automatic once
that target is fixed, but the target field of a genuine developing map is not:
`CartanAtlasTargetCoherence` shows that compatible target values must be
constructed by continuation.  The theorems below are therefore conditional
adapters, not a reduction of the general Cartan globalization boundary.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

open CartanAtlasAutomaticAnchorAlignment

/-- The sharp positive-mean normalized-flow data and the strong
constant-target strict-factor specialization conditionally prove the smooth
global Poincare statement. -/
theorem poincareConjecture_of_fullyAssembledNormalizedFlowMeanLimitPositiveRawData_of_canonicalStrictFactorEndpointTransport
    (raw :
      UniversalFullyAssembledNormalizedFlowMeanLimitPositiveRawData.{u, v})
    (transport :
      UniversalCanonicalStrictFactorEndpointTransportAtlasData.{u}) :
    PoincareConjecture.{u} :=
  poincareConjecture_of_hamiltonConvergenceCore_of_canonicalStrictFactorEndpointTransport
    (universalHamiltonConvergenceCore_of_fullyAssembledNormalizedFlowMeanLimitPositiveRawData
      raw)
    transport

/-- The older scalar-floor provider uses the same constant-target endpoint. -/
theorem poincareConjecture_of_fullyAssembledNormalizedFlowRawData_of_canonicalStrictFactorEndpointTransport
    (raw : UniversalFullyAssembledNormalizedFlowRawData.{u, v})
    (transport :
      UniversalCanonicalStrictFactorEndpointTransportAtlasData.{u}) :
    PoincareConjecture.{u} :=
  poincareConjecture_of_fullyAssembledNormalizedFlowMeanLimitPositiveRawData_of_canonicalStrictFactorEndpointTransport
    raw.toMeanLimitPositive transport

/-- One-point recognition supplies smoothability, while the sharp raw flow and
constant-target transport specialization supply the smooth theorem. -/
theorem poincareConjectureStatement_of_onePointRecognition_of_fullyAssembledNormalizedFlowMeanLimitPositiveRawData_of_canonicalStrictFactorEndpointTransport
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (raw :
      UniversalFullyAssembledNormalizedFlowMeanLimitPositiveRawData.{u, v})
    (transport :
      UniversalCanonicalStrictFactorEndpointTransportAtlasData.{u}) :
    PoincareConjectureStatement.{u} :=
  poincareConjectureStatement_of_exists_smoothability_and_globalPoincareConjecture
    (existsSmoothabilitySmoothManifoldStatement_of_onePointRecognition recognize)
    (poincareConjecture_of_fullyAssembledNormalizedFlowMeanLimitPositiveRawData_of_canonicalStrictFactorEndpointTransport
      raw transport)

/-- The sharp proof-bearing route yields both the smooth and topological
project statements. -/
theorem poincareConjecture_and_statement_of_onePointRecognition_of_fullyAssembledNormalizedFlowMeanLimitPositiveRawData_of_canonicalStrictFactorEndpointTransport
    (recognize : OnePointThreeSpaceRecognitionStatement.{u})
    (raw :
      UniversalFullyAssembledNormalizedFlowMeanLimitPositiveRawData.{u, v})
    (transport :
      UniversalCanonicalStrictFactorEndpointTransportAtlasData.{u}) :
    PoincareConjecture.{u} ∧ PoincareConjectureStatement.{u} :=
  ⟨poincareConjecture_of_fullyAssembledNormalizedFlowMeanLimitPositiveRawData_of_canonicalStrictFactorEndpointTransport
      raw transport,
    poincareConjectureStatement_of_onePointRecognition_of_fullyAssembledNormalizedFlowMeanLimitPositiveRawData_of_canonicalStrictFactorEndpointTransport
      recognize raw transport⟩

/-- Universal finite extinction and topology extraction supply smoothability;
the scalar-floor raw flow and constant-target transport specialization supply
the smooth global Poincare theorem. -/
theorem poincareConjectureStatement_of_universalFiniteExtinction_and_topologyPackage_of_fullyAssembledNormalizedFlowRawData_of_canonicalStrictFactorEndpointTransport
    (finiteExtinction : UniversalFiniteExtinctionStatement.{u})
    (package : ExtinctionTopologyExtractionPackage.{u})
    (raw : UniversalFullyAssembledNormalizedFlowRawData.{u, v})
    (transport :
      UniversalCanonicalStrictFactorEndpointTransportAtlasData.{u}) :
    PoincareConjectureStatement.{u} :=
  poincareConjectureStatement_of_exists_smoothability_and_globalPoincareConjecture
    (existsSmoothabilitySmoothManifoldStatement_of_universalFiniteExtinction_and_topologyPackage
      finiteExtinction package)
    (poincareConjecture_of_fullyAssembledNormalizedFlowRawData_of_canonicalStrictFactorEndpointTransport
      raw transport)

end Poincare
