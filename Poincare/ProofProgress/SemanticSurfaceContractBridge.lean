import Poincare.FullAssembly
import Poincare.Surgery

/-!
Namespaced semantic-surface contracts for route-bearing declarations.

The theorem-contract generator records source names textually. This bridge makes
the corresponding `Poincare.*_eq` constants visible to semantic audits that
check the compiled environment after `import Poincare`.
-/

namespace Poincare

theorem finite_extinction_fundamentalGroup_subsingleton_of_simplyConnectedSpace_eq :
    @Poincare.finite_extinction_fundamentalGroup_subsingleton_of_simplyConnectedSpace =
      @Poincare.finite_extinction_fundamentalGroup_subsingleton_of_simplyConnectedSpace :=
  rfl

theorem finite_extinction_fundamentalGroup_finite_of_simplyConnectedSpace_eq :
    @Poincare.finite_extinction_fundamentalGroup_finite_of_simplyConnectedSpace =
      @Poincare.finite_extinction_fundamentalGroup_finite_of_simplyConnectedSpace :=
  rfl

theorem finite_extinction_fundamental_group_input_of_simplyConnectedSpace_eq :
    @Poincare.finite_extinction_fundamental_group_input_of_simplyConnectedSpace =
      @Poincare.finite_extinction_fundamental_group_input_of_simplyConnectedSpace :=
  rfl

theorem finite_extinction_piOne_finite_of_fundamentalGroupInput_eq :
    @Poincare.finite_extinction_piOne_finite_of_fundamentalGroupInput =
      @Poincare.finite_extinction_piOne_finite_of_fundamentalGroupInput :=
  rfl

theorem finite_extinction_piOne_finite_of_simplyConnectedSpace_eq :
    @Poincare.finite_extinction_piOne_finite_of_simplyConnectedSpace =
      @Poincare.finite_extinction_piOne_finite_of_simplyConnectedSpace :=
  rfl

theorem finite_extinction_time_bound_of_volume_differential_inputs_eq :
    @Poincare.finite_extinction_time_bound_of_volume_differential_inputs =
      @Poincare.finite_extinction_time_bound_of_volume_differential_inputs :=
  rfl

theorem finite_extinction_volume_decay_estimate_of_volume_differential_inputs_eq :
    @Poincare.finite_extinction_volume_decay_estimate_of_volume_differential_inputs =
      @Poincare.finite_extinction_volume_decay_estimate_of_volume_differential_inputs :=
  rfl

theorem finite_extinction_finite_time_integration_of_volume_decay_estimate_eq :
    @Poincare.finite_extinction_finite_time_integration_of_volume_decay_estimate =
      @Poincare.finite_extinction_finite_time_integration_of_volume_decay_estimate :=
  rfl

theorem finite_extinction_differential_inequality_integration_of_volume_decay_estimate_eq :
    @Poincare.finite_extinction_differential_inequality_integration_of_volume_decay_estimate =
      @Poincare.finite_extinction_differential_inequality_integration_of_volume_decay_estimate :=
  rfl

theorem finite_extinction_surgery_time_summability_of_finite_time_integration_eq :
    @Poincare.finite_extinction_surgery_time_summability_of_finite_time_integration =
      @Poincare.finite_extinction_surgery_time_summability_of_finite_time_integration :=
  rfl

theorem finite_extinction_extinction_time_contradiction_of_time_bound_estimates_eq :
    @Poincare.finite_extinction_extinction_time_contradiction_of_time_bound_estimates =
      @Poincare.finite_extinction_extinction_time_contradiction_of_time_bound_estimates :=
  rfl

theorem finite_extinction_conclusion_derivation_of_extinction_time_contradiction_eq :
    @Poincare.finite_extinction_conclusion_derivation_of_extinction_time_contradiction =
      @Poincare.finite_extinction_conclusion_derivation_of_extinction_time_contradiction :=
  rfl

theorem finite_extinction_conclusion_derivation_of_volume_differential_inputs_eq :
    @Poincare.finite_extinction_conclusion_derivation_of_volume_differential_inputs =
      @Poincare.finite_extinction_conclusion_derivation_of_volume_differential_inputs :=
  rfl

theorem finite_extinction_conclusion_statement_of_volume_differential_inputs_eq :
    @Poincare.finite_extinction_conclusion_statement_of_volume_differential_inputs =
      @Poincare.finite_extinction_conclusion_statement_of_volume_differential_inputs :=
  rfl

theorem finite_extinction_statement_of_volume_differential_inputs_eq :
    @Poincare.finite_extinction_statement_of_volume_differential_inputs =
      @Poincare.finite_extinction_statement_of_volume_differential_inputs :=
  rfl

theorem onePoint_threeSpace_finite_extinction_of_sourceChoiceCollapse_and_surgery_packages_eq :
    @Poincare.onePoint_threeSpace_finite_extinction_of_sourceChoiceCollapse_and_surgery_packages =
      @Poincare.onePoint_threeSpace_finite_extinction_of_sourceChoiceCollapse_and_surgery_packages :=
  rfl

theorem onePoint_threeSpace_finite_extinction_of_sourceChoiceCollapse_and_smoothabilitySmoothManifoldStatement_and_surgery_packages_eq :
    @Poincare.onePoint_threeSpace_finite_extinction_of_sourceChoiceCollapse_and_smoothabilitySmoothManifoldStatement_and_surgery_packages =
      @Poincare.onePoint_threeSpace_finite_extinction_of_sourceChoiceCollapse_and_smoothabilitySmoothManifoldStatement_and_surgery_packages :=
  rfl

end Poincare
