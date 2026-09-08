#!/usr/bin/env sh
set -eu

root_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root_dir"

# Portable fallback: use the bundled Python ripgrep subset only when no `rg`
# binary is on PATH (see scripts/bin/rg).
if ! command -v rg >/dev/null 2>&1; then
  PATH="$root_dir/scripts/bin:$PATH"
  export PATH
fi

echo "== Semantic surface audit =="

check_file=
check_dir=
route_parity_dir=
direct_package_parity_dir=
constructor_surface_dir=

cleanup() {
  if [ -n "$check_dir" ]; then
    rm -rf "$check_dir"
  fi
  if [ -n "$check_file" ]; then
    rm -f "$check_file"
  fi
  if [ -n "$route_parity_dir" ]; then
    rm -rf "$route_parity_dir"
  fi
  if [ -n "$direct_package_parity_dir" ]; then
    rm -rf "$direct_package_parity_dir"
  fi
  if [ -n "$constructor_surface_dir" ]; then
    rm -rf "$constructor_surface_dir"
  fi
}

trap cleanup EXIT

check_dir=$(mktemp -d "${TMPDIR:-/tmp}/poincare-semantic-surface.$$-XXXXXX")
check_file="$check_dir/build.log"

# Boundary-extraction requirement-payload forgetful route coverage:
# poincareCompletionCertificate_component_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package_and_boundary_extraction_derivation_target_payload_to_forgetful_dependencies_eq
# poincareCompletionCertificate_package_layer_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package_and_boundary_extraction_derivation_target_payload_to_forgetful_dependencies_eq
# poincareCompletionCertificate_milestone_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package_and_boundary_extraction_derivation_target_payload_to_forgetful_dependencies_eq
# completion_certificate_of_component_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package_and_boundary_extraction_derivation_target_payload_to_forgetful_dependencies_eq
# completion_certificate_of_package_layer_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package_and_boundary_extraction_derivation_target_payload_to_forgetful_dependencies_eq
# completion_certificate_of_milestone_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package_and_boundary_extraction_derivation_target_payload_to_forgetful_dependencies_eq
# completion_certificate_of_component_extraction_derivation_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package_and_boundary_extraction_derivation_target_payload_to_forgetful_dependencies_eq
# completion_certificate_of_package_layer_extraction_derivation_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package_and_boundary_extraction_derivation_target_payload_to_forgetful_dependencies_eq
# completion_certificate_of_milestone_extraction_derivation_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package_and_boundary_extraction_derivation_target_payload_to_forgetful_dependencies_eq

if ! lake build PoincareAudit.Semantic.Surface PoincareAudit.Semantic.CertificateRoutes > "$check_file" 2>&1; then
  cat "$check_file"
  exit 1
fi

topology_package_payload_count=$(
  rg -c 'topology_extraction_payload_of_topology_package' \
    Poincare/DependencyProjections.lean || true
)
if [ "$topology_package_payload_count" != "3" ]; then
  echo "FAIL: dependency topology projections should consume the package extraction payload"
  rg -n 'topology_extraction_payload_of_topology_package' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

topology_package_derivation_payload_count=$(
  rg -c 'topology_extraction_derivation_payload_of_topology_package' \
    Poincare/DependencyProjections.lean || true
)
if [ "$topology_package_derivation_payload_count" != "17" ]; then
  echo "FAIL: dependency topology extraction-derivation projection should consume the package derivation payload across ordinary, boundary, and lifted canonical routes"
  rg -n 'topology_extraction_derivation_payload_of_topology_package' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

topology_package_statement_payload_count=$(
  rg -c 'topology_extraction_statement_payload_of_topology_package' \
    Poincare/DependencyProjections.lean || true
)
if [ "$topology_package_statement_payload_count" != "5" ]; then
  echo "FAIL: dependency topology projections should consume the package extraction statement payload only through dependency payload routes"
  rg -n 'topology_extraction_statement_payload_of_topology_package' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

for raw_topology_projection in \
  extinction_decomposition_of_topology_package \
  extinction_surgery_trace_reconstruction_of_topology_package \
  extinction_surgery_trace_handle_cancellation_of_topology_package \
  extinction_component_classification_of_topology_package \
  extinction_discarded_component_homeomorphism_classification_of_topology_package \
  extinction_component_inventory_of_topology_package \
  extinction_component_boundary_sphere_control_of_topology_package \
  extinction_prime_decomposition_of_topology_package \
  extinction_prime_decomposition_existence_of_topology_package \
  extinction_sphere_theorem_application_of_topology_package \
  extinction_embedded_sphere_production_of_topology_package \
  extinction_loop_theorem_application_of_topology_package \
  extinction_prime_decomposition_compatibility_of_topology_package \
  extinction_prime_factor_uniqueness_of_topology_package \
  extinction_irreducibility_of_topology_package \
  extinction_irreducible_factor_recognition_of_topology_package \
  extinction_connected_sum_collapse_of_topology_package \
  extinction_connected_sum_fundamental_group_control_of_topology_package \
  extinction_connected_sum_van_kampen_of_topology_package \
  extinction_simply_connected_prime_factor_control_of_topology_package \
  extinction_spherical_space_form_reduction_of_topology_package \
  spherical_space_form_classification_of_topology_package \
  spherical_quotient_model_of_topology_package \
  spherical_free_action_of_topology_package \
  spherical_universal_cover_of_topology_package \
  spherical_covering_model_of_topology_package \
  spherical_covering_projection_of_topology_package \
  spherical_fundamental_group_of_topology_package \
  spherical_deck_group_identification_of_topology_package \
  spherical_deck_action_properness_of_topology_package \
  spherical_deck_group_triviality_of_topology_package \
  spherical_deck_action_trivialization_of_topology_package \
  spherical_trivial_deck_quotient_identification_of_topology_package \
  simply_connected_extinction_recognition_of_topology_package \
  trivial_spherical_quotient_of_topology_package \
  trivial_quotient_homeomorphism_of_topology_package \
  spherical_homeomorphism_lift_of_topology_package
do
  if rg -q "\\b${raw_topology_projection}\\b" \
      Poincare/DependencyProjections.lean; then
    echo "FAIL: dependency topology classification projections should consume the dependency classification payload"
    rg -n "\\b${raw_topology_projection}\\b" \
      Poincare/DependencyProjections.lean || true
    exit 1
  fi
done

topology_package_statement_contract_count=$(
  rg -c '\bextinction_topology_extraction_statement_of_topology_package\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$topology_package_statement_contract_count" != "4" ]; then
  echo "FAIL: dependency topology equality contracts should pin the package extraction statement route"
  rg -n '\bextinction_topology_extraction_statement_of_topology_package\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

topology_derivation_payload_contract_count=$(
  rg -c '\btopology_derivation_statement_payload_of_extraction_statement\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$topology_derivation_payload_contract_count" != "4" ]; then
  echo "FAIL: dependency topology equality contracts should pin the derivation statement route"
  rg -n '\btopology_derivation_statement_payload_of_extraction_statement\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

topology_statement_extractor_count=$(
  rg -c '\bextinction_implies_sphere_of_topology_extraction_statement\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$topology_statement_extractor_count" != "8" ]; then
  echo "FAIL: dependency topology statement-route contracts should account for the statement-mediated extractor"
  rg -n '\bextinction_implies_sphere_of_topology_extraction_statement\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

topology_statement_classification_count=$(
  rg -c '\btopology_classification_subobligations_of_derivation_statement\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$topology_statement_classification_count" != "4" ]; then
  echo "FAIL: dependency topology statement-route contracts should account for the classification payload reconstruction"
  rg -n '\btopology_classification_subobligations_of_derivation_statement\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

topology_statement_assembly_count=$(
  rg -c '\btopology_homeomorphism_assembly_statement_of_derivation_statement\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$topology_statement_assembly_count" != "9" ]; then
  echo "FAIL: dependency topology statement-route contracts should account for the homeomorphism assembly statement"
  rg -n '\btopology_homeomorphism_assembly_statement_of_derivation_statement\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

topology_statement_derivation_count=$(
  rg -c '\btopology_homeomorphism_derivation_statement_of_derivation_statement\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$topology_statement_derivation_count" != "9" ]; then
  echo "FAIL: dependency topology statement-route contracts should account for the homeomorphism derivation statement"
  rg -n '\btopology_homeomorphism_derivation_statement_of_derivation_statement\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

if rg -q '\bfinite_extinction_of_surgery_package\b' \
    Poincare/FullAssembly.lean; then
  echo "FAIL: full assembly should consume the named smoothability-and-surgery finite-extinction payload"
  rg -n '\bfinite_extinction_of_surgery_package\b' \
    Poincare/FullAssembly.lean || true
  exit 1
fi

if rg -q '\bextinction_implies_sphere_of_topology_package\b' \
    Poincare/FullAssembly.lean; then
  echo "FAIL: full assembly should consume the package-level topology extraction payload"
  rg -n '\bextinction_implies_sphere_of_topology_package\b' \
    Poincare/FullAssembly.lean || true
  exit 1
fi

if rg -q '\bpoincare_full_assembly_payload_of_surgery_and_topology_packages\b' \
    Poincare/Dependencies.lean; then
  echo "FAIL: aggregate dependency assembly should consume the aggregate assembly input payload"
  rg -n '\bpoincare_full_assembly_payload_of_surgery_and_topology_packages\b' \
    Poincare/Dependencies.lean || true
  exit 1
fi

canonical_payload_bridge_count=$(
  rg -c '\bcanonical_completion_payload_of_poincare_completion_payload\b' \
    Poincare/CompletionTarget.lean || true
)
if [ "$canonical_payload_bridge_count" != "80" ]; then
  echo "FAIL: canonical route payloads and the canonical/project payload iff should consume the shared Poincare-completion bridge"
  rg -n '\bcanonical_completion_payload_of_poincare_completion_payload\b' \
    Poincare/CompletionTarget.lean || true
  exit 1
fi

canonical_statement_payload_bridge_count=$(
  rg -c 'canonical_completion_payload_of_poincare_completion_payload' \
    Poincare/CanonicalBridges.lean || true
)
if [ "$canonical_statement_payload_bridge_count" != "27" ]; then
  echo "FAIL: canonical statement, smooth certificate, and packaged smooth bridges should consume the shared Poincare-completion bridge"
  rg -n 'canonical_completion_payload_of_poincare_completion_payload' \
    Poincare/CanonicalBridges.lean || true
  exit 1
fi

smoothability_statement_payload_count=$(
  rg -c 'smoothability_smooth_structure_statement_payload_of_smoothability_package' \
    Poincare/DependencyProjections.lean || true
)
if [ "$smoothability_statement_payload_count" != "2" ]; then
  echo "FAIL: dependency smoothability projections should consume and contract the package smooth-structure statement payload"
  rg -n 'smoothability_smooth_structure_statement_payload_of_smoothability_package' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

surgery_package_payload_count=$(
  rg -c 'surgery_package_payload_of_dependencies' \
    Poincare/DependencyProjections.lean || true
)
if [ "$surgery_package_payload_count" != "18" ]; then
  echo "FAIL: dependency surgery projections should consume the shared surgery package payload"
  rg -n 'surgery_package_payload_of_dependencies' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

package_routed_dependency_payload_count=$(
  rg -c 'with_surgery_package_of_dependencies' \
    Poincare/DependencyProjections.lean || true
)
if [ "$package_routed_dependency_payload_count" != "33" ]; then
  echo "FAIL: dependency surgery payloads should expose package-routed contracts and consume them"
  rg -n 'with_surgery_package_of_dependencies' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

raw_dependency_surgery_projection_count=$(
  rg -c 'surgery_packages_of_dependencies dependencies M' \
    Poincare/DependencyProjections.lean || true
)
if [ "$raw_dependency_surgery_projection_count" != "3" ]; then
  echo "FAIL: dependency surgery package payload and its equality contracts should be the only direct aggregate surgery projection consumers"
  rg -n 'surgery_packages_of_dependencies dependencies M' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

if rg -q 'surgery_construction_packages_of_dependencies dependencies M' \
    Poincare/DependencyProjections.lean; then
  echo "FAIL: dependency construction payload should consume the shared surgery package payload directly"
  rg -n 'surgery_construction_packages_of_dependencies dependencies M' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

analytic_package_payload_count=$(
  rg -c 'analytic_foundation_payload_of_surgery_package' \
    Poincare/DependencyProjections.lean || true
)
if [ "$analytic_package_payload_count" != "2" ]; then
  echo "FAIL: dependency analytic-foundation projections should consume the surgery analytic payload"
  rg -n 'analytic_foundation_payload_of_surgery_package' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

analytic_payload_raw_flow_count=$(
  rg -c 'ricci_flow_data_of_analytic_foundation_package package' \
    Poincare/DependencyProjections.lean || true
)
if [ "$analytic_payload_raw_flow_count" != "1" ]; then
  echo "FAIL: dependency analytic projections should consume the flow exposed by the analytic payload"
  rg -n 'ricci_flow_data_of_analytic_foundation_package package' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

if rg -q '\banalytic_foundation_payload_of_analytic_foundation_package\b' \
    Poincare/DependencyProjections.lean; then
  echo "FAIL: dependency analytic-foundation projections should stop at the surgery analytic payload"
  rg -n '\banalytic_foundation_payload_of_analytic_foundation_package\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

for raw_analytic_bridge in \
  analytic_foundation_derivation_statement_of_analytic_foundation_package \
  analytic_foundation_statement_of_analytic_foundation_package \
  analytic_foundation_subobligations_of_derivation_statement \
  equation_evidence_of_analytic_foundation_package
do
  if rg -q "\\b${raw_analytic_bridge}\\b" \
      Poincare/DependencyProjections.lean; then
    echo "FAIL: dependency analytic-foundation projections should consume the surgery analytic payload"
    rg -n "\\b${raw_analytic_bridge}\\b" \
      Poincare/DependencyProjections.lean || true
    exit 1
  fi
done

if sed -n '/^theorem equation_evidence_of_surgery_package$/,/^theorem equation_evidence_of_surgery_package_eq$/p' \
    Poincare/Surgery.lean |
    rg -q '\bequation_evidence_of_analytic_foundation_package\b'; then
  echo "FAIL: surgery package equation evidence should consume the surgery analytic payload"
  sed -n '/^theorem equation_evidence_of_surgery_package$/,/^theorem equation_evidence_of_surgery_package_eq$/p' \
    Poincare/Surgery.lean |
    rg -n '\bequation_evidence_of_analytic_foundation_package\b' || true
  exit 1
fi

projection_assembly_inputs_count=$(
  rg -c '\bpoincare_projection_assembly_inputs_payload_of_dependencies\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$projection_assembly_inputs_count" != "16" ]; then
  echo "FAIL: projection target/alias routes should consume the named projection assembly-input payload"
  rg -n '\bpoincare_projection_assembly_inputs_payload_of_dependencies\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

projection_direct_finite_extinction_count=$(
  rg -c '\bfinite_extinction_of_dependencies dependencies\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$projection_direct_finite_extinction_count" != "74" ]; then
  echo "FAIL: finite-extinction projection input should be centralized in projection payloads or explicit route contracts"
  rg -n '\bfinite_extinction_of_dependencies dependencies\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

projection_extraction_derivation_inputs_count=$(
  rg -c '\bpoincare_projection_assembly_inputs_payload_of_extraction_derivation_dependencies\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$projection_extraction_derivation_inputs_count" != "16" ]; then
  echo "FAIL: extraction-derivation target route should consume the extraction-derivation assembly-input payload"
  rg -n '\bpoincare_projection_assembly_inputs_payload_of_extraction_derivation_dependencies\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

topology_extraction_derivation_payload_count=$(
  rg -c '\btopology_extraction_derivation_payload_of_dependencies\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$topology_extraction_derivation_payload_count" != "40" ]; then
  echo "FAIL: extraction-derivation assembly-input payload and statement-route contracts should consume the topology extraction-derivation payload"
  rg -n '\btopology_extraction_derivation_payload_of_dependencies\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

projection_direct_extraction_count=$(
  rg -c '\bextinction_extraction_of_dependencies dependencies\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$projection_direct_extraction_count" != "9" ]; then
  echo "FAIL: topology extraction projection input should be centralized in the projection assembly-input payload or explicit statement-route contract"
  rg -n '\bextinction_extraction_of_dependencies dependencies\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

projection_target_payload_count=$(
  rg -c '\bpoincare_target_payload_of_dependency_projections\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$projection_target_payload_count" != "15" ]; then
  echo "FAIL: projection full/completion routes should consume the projection target payload"
  rg -n '\bpoincare_target_payload_of_dependency_projections\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

projection_extraction_derivation_target_payload_count=$(
  rg -c '\bpoincare_target_payload_of_extraction_derivation_dependency_projections\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$projection_extraction_derivation_target_payload_count" != "14" ]; then
  echo "FAIL: extraction-derivation full/completion routes should consume the extraction-derivation target payload"
  rg -n '\bpoincare_target_payload_of_extraction_derivation_dependency_projections\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

projection_direct_extinction_payload_count=$(
  rg -c '\bpoincare_payload_of_extinction_and_extraction\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$projection_direct_extinction_payload_count" != "10" ]; then
  echo "FAIL: projection final target assembly should be centralized in the projection target payload"
  rg -n '\bpoincare_payload_of_extinction_and_extraction\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

if rg -q 'poincare_completion_payload_of_poincareConjectureStatement target' \
    Poincare/DependencyProjections.lean; then
  echo "FAIL: projection completion payload should reuse the projection target payload criterion"
  rg -n 'poincare_completion_payload_of_poincareConjectureStatement target' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

projection_equation_boundary_target_payload_count=$(
  rg -c '\bpoincare_target_payload_of_equation_boundary_dependency_projections\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$projection_equation_boundary_target_payload_count" != "10" ]; then
  echo "FAIL: equation-boundary projection completion routes should consume the boundary projection target payload"
  rg -n '\bpoincare_target_payload_of_equation_boundary_dependency_projections\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

projection_equation_boundary_extraction_derivation_target_payload_count=$(
  rg -c '\bpoincare_target_payload_of_equation_boundary_extraction_derivation_dependency_projections\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$projection_equation_boundary_extraction_derivation_target_payload_count" != "12" ]; then
  echo "FAIL: equation-boundary certified projection completion routes should consume the boundary certified target payload"
  rg -n '\bpoincare_target_payload_of_equation_boundary_extraction_derivation_dependency_projections\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

projection_equation_boundary_completion_payload_count=$(
  rg -c '\bpoincare_completion_payload_of_equation_boundary_dependency_projections\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$projection_equation_boundary_completion_payload_count" != "15" ]; then
  echo "FAIL: equation-boundary projection statement and criterion routes should consume the boundary projection completion payload"
  rg -n '\bpoincare_completion_payload_of_equation_boundary_dependency_projections\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

projection_equation_boundary_extraction_derivation_completion_payload_count=$(
  rg -c '\bpoincare_completion_payload_of_equation_boundary_extraction_derivation_dependency_projections\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$projection_equation_boundary_extraction_derivation_completion_payload_count" != "17" ]; then
  echo "FAIL: equation-boundary certified projection statement and criterion routes should consume the boundary certified completion payload"
  rg -n '\bpoincare_completion_payload_of_equation_boundary_extraction_derivation_dependency_projections\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

projection_equation_boundary_canonical_statement_count=$(
  rg -c '\bcanonical_three_sphere_statement_of_equation_boundary_dependency_projections\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$projection_equation_boundary_canonical_statement_count" != "7" ]; then
  echo "FAIL: equation-boundary projection canonical endpoints should expose theorem, equality, topology, package, direct-verification, and forgetful routes"
  rg -n '\bcanonical_three_sphere_statement_of_equation_boundary_dependency_projections\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

projection_equation_boundary_extraction_derivation_canonical_statement_count=$(
  rg -c '\bcanonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependency_projections\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$projection_equation_boundary_extraction_derivation_canonical_statement_count" != "10" ]; then
  echo "FAIL: equation-boundary certified projection canonical endpoints should expose theorem, equality, statement, finite-extinction, extraction-derivation, package, direct-verification, forgetful, boundary-route, and lifted-certificate routes"
  rg -n '\bcanonical_three_sphere_statement_of_equation_boundary_extraction_derivation_dependency_projections\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

projection_equation_boundary_lifted_homeomorphism_canonical_statement_count=$(
  rg -c '\bcanonical_three_sphere_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$projection_equation_boundary_lifted_homeomorphism_canonical_statement_count" != "9" ]; then
  echo "FAIL: equation-boundary lifted-homeomorphism projection canonical endpoints should expose theorem, equality, statement, finite-extinction, package, direct-verification, forgetful, certified, and boundary routes"
  rg -n '\bcanonical_three_sphere_statement_of_equation_boundary_lifted_homeomorphism_derivation_dependency_projections\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

projection_equation_boundary_completion_criterion_count=$(
  rg -c '\bcompletion_criterion_of_equation_boundary_dependency_projections\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$projection_equation_boundary_completion_criterion_count" != "7" ]; then
  echo "FAIL: equation-boundary projection criterion endpoints should expose theorem, equality, topology, package, direct-verification, and forgetful routes"
  rg -n '\bcompletion_criterion_of_equation_boundary_dependency_projections\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

projection_equation_boundary_extraction_derivation_completion_criterion_count=$(
  rg -c '\bcompletion_criterion_of_equation_boundary_extraction_derivation_dependency_projections\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$projection_equation_boundary_extraction_derivation_completion_criterion_count" != "9" ]; then
  echo "FAIL: equation-boundary certified projection criterion endpoints should expose theorem, equality, statement, finite-extinction, direct-verification, forgetful, and boundary routes"
  rg -n '\bcompletion_criterion_of_equation_boundary_extraction_derivation_dependency_projections\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

canonical_completion_equation_boundary_payload_count=$(
  rg -c '\bcanonical_completion_payload_of_equation_boundary_dependency_projections\b' \
    Poincare/CompletionTarget.lean || true
)
if [ "$canonical_completion_equation_boundary_payload_count" != "15" ]; then
  echo "FAIL: equation-boundary projection canonical completion payload endpoints should expose theorem, equality, topology, finite-extinction, direct-verification, package, forgetful, and remaining-dependency routes"
  rg -n '\bcanonical_completion_payload_of_equation_boundary_dependency_projections\b' \
    Poincare/CompletionTarget.lean || true
  exit 1
fi

canonical_completion_equation_boundary_target_count=$(
  rg -c '\bcanonical_completion_target_of_equation_boundary_dependency_projections\b' \
    Poincare/CompletionTarget.lean || true
)
if [ "$canonical_completion_equation_boundary_target_count" != "13" ]; then
  echo "FAIL: equation-boundary projection canonical completion target endpoints should expose theorem, equality, topology, finite-extinction, direct-verification, package, forgetful, remaining-dependency, and project-statement routes"
  rg -n '\bcanonical_completion_target_of_equation_boundary_dependency_projections\b' \
    Poincare/CompletionTarget.lean || true
  exit 1
fi

canonical_completion_equation_boundary_criterion_count=$(
  rg -c '\bcanonical_completion_criterion_of_equation_boundary_dependency_projections\b' \
    Poincare/CompletionTarget.lean || true
)
if [ "$canonical_completion_equation_boundary_criterion_count" != "14" ]; then
  echo "FAIL: equation-boundary projection canonical completion criterion endpoints should expose theorem, equality, topology, finite-extinction, direct-verification, package, forgetful, remaining-dependency, project-criterion, and certificate routes"
  rg -n '\bcanonical_completion_criterion_of_equation_boundary_dependency_projections\b' \
    Poincare/CompletionTarget.lean || true
  exit 1
fi

canonical_completion_equation_boundary_extraction_derivation_payload_count=$(
  rg -c '\bcanonical_completion_payload_of_equation_boundary_extraction_derivation_dependency_projections\b' \
    Poincare/CompletionTarget.lean || true
)
if [ "$canonical_completion_equation_boundary_extraction_derivation_payload_count" != "20" ]; then
  echo "FAIL: equation-boundary certified projection canonical completion payload endpoints should expose theorem, equality, statement, finite-extinction, direct-verification, package, extraction-derivation, forgetful, remaining-dependency, boundary-route, and aggregate lifted-certificate routes"
  rg -n '\bcanonical_completion_payload_of_equation_boundary_extraction_derivation_dependency_projections\b' \
    Poincare/CompletionTarget.lean || true
  exit 1
fi

canonical_completion_equation_boundary_extraction_derivation_target_count=$(
  rg -c '\bcanonical_completion_target_of_equation_boundary_extraction_derivation_dependency_projections\b' \
    Poincare/CompletionTarget.lean || true
)
if [ "$canonical_completion_equation_boundary_extraction_derivation_target_count" != "19" ]; then
  echo "FAIL: equation-boundary certified projection canonical completion target endpoints should expose theorem, equality, statement, finite-extinction, direct-verification, package, extraction-derivation, forgetful, remaining-dependency, project-statement, canonical-statement, boundary-route, and aggregate lifted-certificate routes"
  rg -n '\bcanonical_completion_target_of_equation_boundary_extraction_derivation_dependency_projections\b' \
    Poincare/CompletionTarget.lean || true
  exit 1
fi

canonical_completion_equation_boundary_extraction_derivation_criterion_count=$(
  rg -c '\bcanonical_completion_criterion_of_equation_boundary_extraction_derivation_dependency_projections\b' \
    Poincare/CompletionTarget.lean || true
)
if [ "$canonical_completion_equation_boundary_extraction_derivation_criterion_count" != "23" ]; then
  echo "FAIL: equation-boundary certified projection canonical completion criterion endpoints should expose theorem, equality, statement, finite-extinction, direct-verification, package, extraction-derivation, forgetful, remaining-dependency, project-criterion, boundary-route, certificate, and aggregate lifted-certificate routes"
  rg -n '\bcanonical_completion_criterion_of_equation_boundary_extraction_derivation_dependency_projections\b' \
    Poincare/CompletionTarget.lean || true
  exit 1
fi

canonical_completion_equation_boundary_completion_payload_count=$(
  rg -c '\bpoincare_completion_payload_of_equation_boundary_dependency_projections\b' \
    Poincare/CompletionTarget.lean || true
)
if [ "$canonical_completion_equation_boundary_completion_payload_count" != "4" ]; then
  echo "FAIL: equation-boundary canonical completion payload route should consume the named boundary projection completion payload"
  rg -n '\bpoincare_completion_payload_of_equation_boundary_dependency_projections\b' \
    Poincare/CompletionTarget.lean || true
  exit 1
fi

canonical_completion_equation_boundary_extraction_derivation_completion_payload_count=$(
  rg -c '\bpoincare_completion_payload_of_equation_boundary_extraction_derivation_dependency_projections\b' \
    Poincare/CompletionTarget.lean || true
)
if [ "$canonical_completion_equation_boundary_extraction_derivation_completion_payload_count" != "6" ]; then
  echo "FAIL: equation-boundary certified canonical completion payload routes should consume the named boundary certified projection completion payload"
  rg -n '\bpoincare_completion_payload_of_equation_boundary_extraction_derivation_dependency_projections\b' \
    Poincare/CompletionTarget.lean || true
  exit 1
fi

aggregate_target_payload_count=$(
  rg -c '\bpoincare_target_payload_of_aggregate_dependencies\b' \
    Poincare/Dependencies.lean || true
)
if [ "$aggregate_target_payload_count" != "9" ]; then
  echo "FAIL: aggregate dependency target, completion, and equation-boundary routes should consume the aggregate target payload"
  rg -n '\bpoincare_target_payload_of_aggregate_dependencies\b' \
    Poincare/Dependencies.lean || true
  exit 1
fi

aggregate_extraction_derivation_target_payload_count=$(
  rg -c '\bpoincare_target_payload_of_aggregate_extraction_derivation_dependencies\b' \
    Poincare/Dependencies.lean || true
)
if [ "$aggregate_extraction_derivation_target_payload_count" != "12" ]; then
  echo "FAIL: aggregate extraction-derivation and equation-boundary dependency routes should consume the certified aggregate target payload"
  rg -n '\bpoincare_target_payload_of_aggregate_extraction_derivation_dependencies\b' \
    Poincare/Dependencies.lean || true
  exit 1
fi

equation_boundary_target_payload_count=$(
  rg -c '\bpoincare_target_payload_of_equation_boundary_dependencies\b' \
    Poincare/Dependencies.lean || true
)
if [ "$equation_boundary_target_payload_count" != "10" ]; then
  echo "FAIL: equation-boundary full assembly and verification-family routes should consume the boundary-preserving target payload"
  rg -n '\bpoincare_target_payload_of_equation_boundary_dependencies\b' \
    Poincare/Dependencies.lean || true
  exit 1
fi

equation_boundary_extraction_derivation_target_payload_count=$(
  rg -c '\bpoincare_target_payload_of_equation_boundary_extraction_derivation_dependencies\b' \
    Poincare/Dependencies.lean || true
)
if [ "$equation_boundary_extraction_derivation_target_payload_count" != "11" ]; then
  echo "FAIL: equation-boundary certified full assembly routes should consume the boundary-preserving certified target payload"
  rg -n '\bpoincare_target_payload_of_equation_boundary_extraction_derivation_dependencies\b' \
    Poincare/Dependencies.lean || true
  exit 1
fi

aggregate_extraction_derivation_completion_payload_count=$(
  rg -c '\bpoincare_completion_payload_of_aggregate_extraction_derivation_dependencies\b' \
    Poincare/Dependencies.lean || true
)
if [ "$aggregate_extraction_derivation_completion_payload_count" != "11" ]; then
  echo "FAIL: aggregate extraction-derivation statement and criterion should consume the certified completion payload"
  rg -n '\bpoincare_completion_payload_of_aggregate_extraction_derivation_dependencies\b' \
    Poincare/Dependencies.lean || true
  exit 1
fi

equation_boundary_extraction_derivation_completion_payload_count=$(
  rg -c '\bpoincare_completion_payload_of_equation_boundary_extraction_derivation_dependencies\b' \
    Poincare/Dependencies.lean || true
)
if [ "$equation_boundary_extraction_derivation_completion_payload_count" != "11" ]; then
  echo "FAIL: equation-boundary extraction-derivation statement and criterion should consume the strengthened certified completion payload"
  rg -n '\bpoincare_completion_payload_of_equation_boundary_extraction_derivation_dependencies\b' \
    Poincare/Dependencies.lean || true
  exit 1
fi

explicit_target_payload_count=$(
  rg -c '\bpoincare_target_payload_of_surgery_and_topology_packages\b' \
    Poincare/FullAssembly.lean || true
)
if [ "$explicit_target_payload_count" != "9" ]; then
  echo "FAIL: explicit package full/completion and statement-route contracts should consume the explicit target payload"
  rg -n '\bpoincare_target_payload_of_surgery_and_topology_packages\b' \
    Poincare/FullAssembly.lean || true
  exit 1
fi

explicit_direct_extinction_payload_count=$(
  rg -c 'poincare_payload_of_extinction_and_extraction' \
    Poincare/FullAssembly.lean || true
)
if [ "$explicit_direct_extinction_payload_count" != "2" ]; then
  echo "FAIL: explicit package final target assembly should be centralized in the explicit target payload"
  rg -n 'poincare_payload_of_extinction_and_extraction' \
    Poincare/FullAssembly.lean || true
  exit 1
fi

if rg -q 'poincare_completion_payload_of_poincareConjectureStatement target' \
    Poincare/FullAssembly.lean; then
  echo "FAIL: explicit package completion payload should reuse the explicit target payload criterion"
  rg -n 'poincare_completion_payload_of_poincareConjectureStatement target' \
    Poincare/FullAssembly.lean || true
  exit 1
fi

remaining_dependency_payload_count=$(
  rg -c 'poincare_completion_payload_of_remaining_dependency_package\b' \
    Poincare/CompletionTarget.lean || true
)
if [ "$remaining_dependency_payload_count" != "36" ]; then
  echo "FAIL: canonical dependency payload should consume the named remaining dependency payload"
  rg -n 'poincare_completion_payload_of_remaining_dependency_package\b' \
    Poincare/CompletionTarget.lean || true
  exit 1
fi

direct_remaining_dependency_completion_count=$(
  rg -c 'poincare_completion_payload_of_dependencies dependencies' \
    Poincare/CompletionTarget.lean || true
)
if [ "$direct_remaining_dependency_completion_count" != "2" ]; then
  echo "FAIL: aggregate completion payload should only be called inside the remaining dependency payload"
  rg -n 'poincare_completion_payload_of_dependencies dependencies' \
    Poincare/CompletionTarget.lean || true
  exit 1
fi

aggregate_direct_extinction_payload_count=$(
  rg -c '\bpoincare_payload_of_extinction_and_extraction\b' \
    Poincare/Dependencies.lean || true
)
if [ "$aggregate_direct_extinction_payload_count" != "2" ]; then
  echo "FAIL: aggregate dependency final target assembly should be centralized in the aggregate target payload"
  rg -n '\bpoincare_payload_of_extinction_and_extraction\b' \
    Poincare/Dependencies.lean || true
  exit 1
fi

if rg -q 'poincare_completion_payload_of_poincareConjectureStatement target' \
    Poincare/Dependencies.lean; then
  echo "FAIL: aggregate completion payload should reuse the aggregate target payload criterion"
  rg -n 'poincare_completion_payload_of_poincareConjectureStatement target' \
    Poincare/Dependencies.lean || true
  exit 1
fi

smoothability_bridge_payload_count=$(
  rg -c 'smoothability_bridge_payload_of_smoothability_package' \
    Poincare/DependencyProjections.lean || true
)
if [ "$smoothability_bridge_payload_count" != "1" ]; then
  echo "FAIL: dependency smoothability projections should consume the package bridge payload"
  rg -n 'smoothability_bridge_payload_of_smoothability_package' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

for raw_smoothability_bridge in \
  smooth_structure_derivation_statement_of_smoothability_package \
  smoothability_bridge_derivation_of_smoothability_package \
  smooth_model_compatibility_of_smoothability_package \
  smooth_chart_compatibility_of_smoothability_package \
  smoothability_subobligations_of_derivation_statement
do
  raw_smoothability_bridge_count=$(
    rg -c "\\b${raw_smoothability_bridge}\\b" \
      Poincare/DependencyProjections.lean || true
  )
  if [ "$raw_smoothability_bridge_count" != "1" ]; then
    echo "FAIL: dependency smoothability projections should expose exactly one equality contract for ${raw_smoothability_bridge}"
    rg -n "\\b${raw_smoothability_bridge}\\b" \
      Poincare/DependencyProjections.lean || true
    exit 1
  fi
done

surgery_package_payload_count=$(
  rg -c 'surgery_construction_payload_of_construction_package' \
    Poincare/DependencyProjections.lean || true
)
if [ "$surgery_package_payload_count" != "2" ]; then
  echo "FAIL: dependency surgery projections bypass the construction package payload"
  rg -n 'surgery_construction_payload_of_construction_package' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

if rg -q '\bsurgery_construction_subobligations_of_statement\b' \
    Poincare/DependencyProjections.lean; then
  echo "FAIL: dependency surgery projections should consume the construction package payload"
  rg -n '\bsurgery_construction_subobligations_of_statement\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

perelman_package_payload_count=$(
  rg -c 'perelman_control_payload_of_package' \
    Poincare/DependencyProjections.lean || true
)
if [ "$perelman_package_payload_count" != "2" ]; then
  echo "FAIL: dependency Perelman projections bypass the package payload"
  rg -n 'perelman_control_payload_of_package' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

if rg -q '\bperelman_subobligations_of_statement\b' \
    Poincare/DependencyProjections.lean; then
  echo "FAIL: dependency Perelman projections should consume the package payload"
  rg -n '\bperelman_subobligations_of_statement\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

if rg -q '\bperelman_monotonicity_blowup_subobligations_of_statement\b' \
    Poincare/DependencyProjections.lean; then
  echo "FAIL: dependency Perelman projections should consume the package payload"
  rg -n '\bperelman_monotonicity_blowup_subobligations_of_statement\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

if rg -q 'finite_extinction_subobligations_payload_of_surgery_package' \
    Poincare/DependencyProjections.lean; then
  echo "FAIL: dependency finite-extinction projections should use the package-routed named statement reconstruction"
  rg -n 'finite_extinction_subobligations_payload_of_surgery_package' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

if rg -q 'finite_extinction_statement_payload_of_surgery_package' \
    Poincare/DependencyProjections.lean; then
  echo "FAIL: dependency finite-extinction projections should use the package-routed named statement reconstruction"
  rg -n 'finite_extinction_statement_payload_of_surgery_package' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

finite_extinction_width_statement_route_count=$(
  rg -c '\bfinite_extinction_width_subobligations_of_statement\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$finite_extinction_width_statement_route_count" != "2" ]; then
  echo "FAIL: dependency finite-extinction package-routed payload and contract should rebuild the named width sub-obligations"
  rg -n '\bfinite_extinction_width_subobligations_of_statement\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

finite_extinction_full_statement_route_count=$(
  rg -c '\bfinite_extinction_subobligations_of_statement\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$finite_extinction_full_statement_route_count" != "2" ]; then
  echo "FAIL: dependency finite-extinction package-routed payload and contract should rebuild the named full sub-obligations"
  rg -n '\bfinite_extinction_subobligations_of_statement\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

finite_extinction_derivation_statement_route_count=$(
  rg -c '\bfinite_extinction_derivation_of_subobligations_statement\b' \
    Poincare/DependencyProjections.lean || true
)
if [ "$finite_extinction_derivation_statement_route_count" != "5" ]; then
  echo "FAIL: dependency finite-extinction package-routed payload should type and build the derivation route"
  rg -n '\bfinite_extinction_derivation_of_subobligations_statement\b' \
    Poincare/DependencyProjections.lean || true
  exit 1
fi

# Attribute-prefixed route checks included in the full surface guard.

audit_surface_declarations="$check_dir/audit-surface-declarations"
audit_surface_tokens="$check_dir/audit-surface-tokens"
audit_surface_missing="$check_dir/audit-surface-missing"
all_surface_declarations="$check_dir/all-surface-declarations"
parser_check_file="$check_dir/parser-visible-check.lean"
generated_check_tokens="$check_dir/generated-check-tokens"
generated_check_missing="$check_dir/generated-check-missing"
generated_check_stale="$check_dir/generated-check-stale"
manual_check_tokens="$check_dir/manual-check-tokens"
manual_check_stale="$check_dir/manual-check-stale"
rg -P --no-filename -o '^(?:@\[[^]\n]+\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|structure|class|inductive|abbrev|instance)\s+[A-Za-z0-9_]+(?=\s*(?:\.|:|:=|where|extends|$|\[|\(|\{|⦃))' \
  Poincare.lean Poincare/*.lean |
  awk '{ print $NF }' |
  awk '/payload|target|criterion|certificate|statement|poincare_conjecture|route|projection|dependency|dependencies|bridge|finite_extinction|equation_boundary/' |
  sort -u > "$audit_surface_declarations"

rg --no-filename -o '[A-Za-z0-9_]+' audit/PoincareAudit/Semantic/*.lean |
  sort -u > "$audit_surface_tokens"

comm -23 "$audit_surface_declarations" "$audit_surface_tokens" > "$audit_surface_missing"

if [ -s "$audit_surface_missing" ]; then
  echo "FAIL: semantic surface audit is missing route-bearing Poincare declarations"
  sed 's/^/MISSING: /' "$audit_surface_missing"
  exit 1
else
  echo "PASS: semantic surface audit covers route-bearing Poincare declarations"
fi

rg -P --no-filename -o '^(?:@\[[^]\n]+\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|structure|class|inductive|abbrev|instance)\s+[A-Za-z0-9_]+(?=\s*(?:\.|:|:=|where|extends|$|\[|\(|\{|⦃))' \
  Poincare.lean Poincare/*.lean |
  awk '{ print $NF }' |
  sort -u > "$all_surface_declarations"

{
  printf 'import Poincare\n\n'
  printf 'open Poincare\n'
  printf 'open RicciFlow\n'
  printf 'open RicciFlow.RicciFlow\n'
  printf 'open CovariantDerivative\n\n'
  while IFS= read -r declaration_name; do
    printf '#check %s\n' "$declaration_name"
  done < "$all_surface_declarations"
} > "$parser_check_file"

if ! lake env lean "$parser_check_file" >/dev/null 2>&1; then
  lake env lean "$parser_check_file" || true
  exit 1
fi

rg --no-filename -o '#check [A-Za-z0-9_]+' "$parser_check_file" |
  awk '{ print $2 }' |
  sort -u > "$generated_check_tokens"

comm -23 "$all_surface_declarations" "$generated_check_tokens" > "$generated_check_missing"

if [ -s "$generated_check_missing" ]; then
  echo "FAIL: semantic surface audit generated parser-visible #check lines missed Poincare declarations"
  sed 's/^/MISSING: /' "$generated_check_missing"
  exit 1
else
  echo "PASS: semantic surface audit generated #checks for all parser-visible Poincare declarations"
fi

comm -13 "$all_surface_declarations" "$generated_check_tokens" > "$generated_check_stale"

if [ -s "$generated_check_stale" ]; then
  echo "FAIL: semantic surface audit generated stale #check lines without parser-visible Poincare declarations"
  sed 's/^/STALE: /' "$generated_check_stale"
  exit 1
else
  echo "PASS: semantic surface audit generated no stale parser-visible #check lines"
fi

rg --no-filename -o '#check Poincare\.[A-Za-z0-9_]+' audit/PoincareAudit/Semantic/*.lean |
  awk -F. '{ print $NF }' |
  sort -u > "$manual_check_tokens"

comm -13 "$all_surface_declarations" "$manual_check_tokens" > "$manual_check_stale"

if [ -s "$manual_check_stale" ]; then
  echo "FAIL: semantic surface audit has stale manual #check lines without parser-visible Poincare declarations"
  sed 's/^/STALE: /' "$manual_check_stale"
  exit 1
else
  echo "PASS: semantic surface audit has no stale manual #check lines"
fi

constructor_surface_dir=$(mktemp -d "${TMPDIR:-/tmp}/poincare-semantic-constructor-surface.$$-XXXXXX")
constructor_surface_constructors="$constructor_surface_dir/constructors"
constructor_surface_boundary_constructors="$constructor_surface_dir/boundary-constructors"
constructor_surface_endpoints="$constructor_surface_dir/endpoints"
constructor_surface_missing="$constructor_surface_dir/missing"

perl -0ne 'while (/^theorem\s+(completion_certificate_of_[A-Za-z0-9_]+)\b(.*?)(?=^theorem\s+|\z)/msg) { my ($n,$b)=($1,$2); next if $n =~ /_eq$/; next if $n =~ /_of_completion_certificate(?:_|$)/; next unless $b =~ /:\s*PoincareCompletionCertificate\.\{u\}/s; print "$n\n"; }' \
  Poincare/CompletionTarget.lean | sort -u > "$constructor_surface_constructors"

if [ ! -s "$constructor_surface_constructors" ]; then
  echo "FAIL: semantic constructor surface found no completion certificate constructors"
  exit 1
fi

check_completion_certificate_constructor_endpoint_family() {
  endpoint_family="$1"
  label="$2"

  if printf '%s\n' "$endpoint_family" | rg -q 'completion_certificate'; then
    rg --no-filename -o "^theorem ${endpoint_family}_([A-Za-z0-9_]+)\b" \
      -r 'completion_certificate_of_$1' \
      Poincare/CanonicalBridges.lean Poincare/CompletionTarget.lean |
      sed '/_eq$/d' |
      sort -u > "$constructor_surface_endpoints"
  else
    rg --no-filename -o "^theorem ${endpoint_family}_completion_certificate_of_([A-Za-z0-9_]+)\b" \
      -r 'completion_certificate_of_$1' \
      Poincare/CanonicalBridges.lean Poincare/CompletionTarget.lean |
      sed '/_eq$/d' |
      sort -u > "$constructor_surface_endpoints"
  fi

  comm -23 "$constructor_surface_constructors" "$constructor_surface_endpoints" \
    > "$constructor_surface_missing"

  if [ -s "$constructor_surface_missing" ]; then
    echo "FAIL: semantic completion certificate constructors without ${label} endpoints"
    sed 's/^/MISSING: /' "$constructor_surface_missing"
    exit 1
  else
    echo "PASS: semantic completion certificate constructors expose ${label} endpoints"
  fi
}

check_completion_certificate_constructor_endpoint_family \
  poincare_conjecture_of reserved-theorem
check_completion_certificate_constructor_endpoint_family \
  poincare_conjecture_payload_of reserved-payload
check_completion_certificate_constructor_endpoint_family \
  target_statement_of target-statement
check_completion_certificate_constructor_endpoint_family \
  canonical_completion_payload_of canonical-payload
check_completion_certificate_constructor_endpoint_family \
  poincare_completion_payload_of project-payload
check_completion_certificate_constructor_endpoint_family \
  canonical_completion_target_of canonical-target
check_completion_certificate_constructor_endpoint_family \
  completion_criterion_of completion-criterion
check_completion_certificate_constructor_endpoint_family \
  canonical_completion_criterion_of canonical-criterion
check_completion_certificate_constructor_endpoint_family \
  poincare_full_assembly_payload_of full-assembly
check_completion_certificate_constructor_endpoint_family \
  poincare_full_assembly_payload_of_completion_certificate_extraction_derivation_of certified-full-assembly

for payload_route_family in theoremName literal canonical_statement aggregate_canonical_statement aggregate_dependency project_statement; do
  rg --no-filename -o "^theorem poincareCompletionCertificate_${payload_route_family}_payload_of_completion_certificate_of_([A-Za-z0-9_]+)_eq\b" \
    -r 'completion_certificate_of_$1' \
    Poincare/CanonicalBridges.lean Poincare/CompletionTarget.lean |
    sort -u > "$constructor_surface_endpoints"

  comm -23 "$constructor_surface_constructors" "$constructor_surface_endpoints" \
    > "$constructor_surface_missing"

  if [ -s "$constructor_surface_missing" ]; then
    echo "FAIL: semantic completion certificate constructors without ${payload_route_family} payload routes"
    sed 's/^/MISSING: /' "$constructor_surface_missing"
    exit 1
  else
    echo "PASS: semantic completion certificate constructors expose ${payload_route_family} payload routes"
  fi
done

perl -0ne 'while (/^theorem\s+(completion_certificate_with_equation_boundary_verification_payload_of_[A-Za-z0-9_]+)\b(.*?)(?=^theorem\s+|\z)/msg) { my ($n,$b)=($1,$2); next if $n =~ /_eq$/; next unless $b =~ /:\s*PoincareCompletionCertificateWithEquationBoundaryVerificationPayload\.\{u\}/s; print "$n\n"; }' \
  Poincare/CompletionTarget.lean Poincare/CanonicalBridges.lean |
  sort -u > "$constructor_surface_boundary_constructors"

if [ ! -s "$constructor_surface_boundary_constructors" ]; then
  echo "FAIL: semantic constructor surface found no boundary-aware completion certificate constructors"
  exit 1
fi

for boundary_endpoint_family in \
    poincare_completion_payload_of_completion_certificate_with_equation_boundary_verification_payload \
    target_statement_of_completion_certificate_with_equation_boundary_verification_payload \
    canonical_completion_target_of_completion_certificate_with_equation_boundary_verification_payload \
    poincare_conjecture_of_completion_certificate_with_equation_boundary_verification_payload \
    poincare_conjecture_payload_of_completion_certificate_with_equation_boundary_verification_payload \
    completion_criterion_of_completion_certificate_with_equation_boundary_verification_payload \
    canonical_completion_criterion_of_completion_certificate_with_equation_boundary_verification_payload \
    poincare_full_assembly_payload_of_completion_certificate_with_equation_boundary_verification_payload \
    poincare_full_assembly_payload_of_completion_certificate_with_equation_boundary_verification_payload_extraction_derivation \
    canonical_three_sphere_statement_of_completion_certificate_with_equation_boundary_verification_payload \
    poincareCompletionCertificate_canonical_statement_payload_of_completion_certificate_with_equation_boundary_verification_payload \
    poincareCompletionCertificate_aggregate_canonical_statement_payload_of_completion_certificate_with_equation_boundary_verification_payload; do
  rg --no-filename -o "^theorem ${boundary_endpoint_family}_of_([A-Za-z0-9_]+)\b" \
    -r 'completion_certificate_with_equation_boundary_verification_payload_of_$1' \
    Poincare/CanonicalBridges.lean Poincare/CompletionTarget.lean |
    sed '/_eq$/d' |
    sort -u > "$constructor_surface_endpoints"

  comm -23 "$constructor_surface_boundary_constructors" "$constructor_surface_endpoints" \
    > "$constructor_surface_missing"

  if [ -s "$constructor_surface_missing" ]; then
    echo "FAIL: semantic boundary-aware completion certificate constructors without ${boundary_endpoint_family}"
    sed 's/^/MISSING: /' "$constructor_surface_missing"
    exit 1
  else
    echo "PASS: semantic boundary-aware completion certificate constructors expose ${boundary_endpoint_family}"
  fi
done

for boundary_payload_family in theoremName literal canonical_statement aggregate_canonical_statement aggregate_dependency project_statement; do
  rg --no-filename -o "^theorem poincareCompletionCertificate_${boundary_payload_family}_payload_of_completion_certificate_with_equation_boundary_verification_payload_of_([A-Za-z0-9_]+)_eq\b" \
    -r 'completion_certificate_with_equation_boundary_verification_payload_of_$1' \
    Poincare/CanonicalBridges.lean Poincare/CompletionTarget.lean |
    sort -u > "$constructor_surface_endpoints"

  comm -23 "$constructor_surface_boundary_constructors" "$constructor_surface_endpoints" \
    > "$constructor_surface_missing"

  if [ -s "$constructor_surface_missing" ]; then
    echo "FAIL: semantic boundary-aware completion certificate constructors without ${boundary_payload_family} payload equality routes"
    sed 's/^/MISSING: /' "$constructor_surface_missing"
    exit 1
  else
    echo "PASS: semantic boundary-aware completion certificate constructors expose ${boundary_payload_family} payload equality routes"
  fi
done

route_parity_dir=$(mktemp -d "${TMPDIR:-/tmp}/poincare-semantic-route-parity.$$-XXXXXX")
awk '/^theorem / {print $2}' \
  Poincare/CompletionTarget.lean Poincare/CanonicalBridges.lean \
  > "$route_parity_dir/theorems"
sed -n 's/^poincareCompletionCertificate_theoremName_payload_of_completion_certificate_of_\(.*\)_eq$/\1/p' \
  "$route_parity_dir/theorems" | sort -u > "$route_parity_dir/theoremName.routes"
for family in literal canonical_statement aggregate_canonical_statement aggregate_dependency project_statement; do
  sed -n "s/^poincareCompletionCertificate_${family}_payload_of_completion_certificate_of_\\(.*\\)_eq$/\\1/p" \
    "$route_parity_dir/theorems" | sort -u > "$route_parity_dir/${family}.routes"
  missing_theorem_name=$(comm -13 "$route_parity_dir/theoremName.routes" "$route_parity_dir/${family}.routes")
  missing_family=$(comm -23 "$route_parity_dir/theoremName.routes" "$route_parity_dir/${family}.routes")
  {
    sed -n "s/^completion_certificate_of_${family}_payload_of_\\(.*\\)_eq$/\\1/p" \
      "$route_parity_dir/theorems"
    sed -n "s/^completion_certificate_of_${family}_payload_of_completion_certificate_of_\\(.*\\)_eq$/\\1/p" \
      "$route_parity_dir/theorems"
  } | sort -u > "$route_parity_dir/${family}.constructor.routes"
  missing_constructor=$(comm -23 "$route_parity_dir/${family}.routes" "$route_parity_dir/${family}.constructor.routes")

  if [ -n "$missing_theorem_name" ]; then
    echo "FAIL: semantic $family payload routes without theorem-name payload counterparts"
    printf '%s\n' "$missing_theorem_name" | sed 's/^/MISSING: /'
    exit 1
  else
    echo "PASS: semantic $family payload routes have theorem-name payload counterparts"
  fi

  if [ -n "$missing_family" ]; then
    echo "FAIL: semantic theorem-name payload routes without $family payload counterparts"
    printf '%s\n' "$missing_family" | sed 's/^/MISSING: /'
    exit 1
  else
    echo "PASS: semantic theorem-name payload routes have $family payload counterparts"
  fi

  if [ -n "$missing_constructor" ]; then
    echo "FAIL: semantic $family payload projection routes without constructor counterparts"
    printf '%s\n' "$missing_constructor" | sed 's/^/MISSING: /'
    exit 1
  else
    echo "PASS: semantic $family payload projection routes have constructor counterparts"
  fi

  sed -n 's/^poincareCompletionCertificate_theoremName_payload_of_completion_certificate_with_equation_boundary_verification_payload_of_\(.*\)_eq$/\1/p' \
    "$route_parity_dir/theorems" | sort -u > "$route_parity_dir/boundary.theoremName.routes"
  sed -n "s/^poincareCompletionCertificate_${family}_payload_of_completion_certificate_with_equation_boundary_verification_payload_of_\\(.*\\)_eq$/\\1/p" \
    "$route_parity_dir/theorems" | sort -u > "$route_parity_dir/boundary.${family}.routes"
  {
    sed -n "s/^completion_certificate_of_${family}_payload_of_completion_certificate_with_equation_boundary_verification_payload_of_\\(.*\\)_eq$/\\1/p" \
      "$route_parity_dir/theorems"
    sed -n "s/^completion_certificate_of_${family}_payload_of_poincareCompletionCertificate_${family}_payload_of_completion_certificate_with_equation_boundary_verification_payload_of_\\(.*\\)_eq$/\\1/p" \
      "$route_parity_dir/theorems"
  } | sort -u > "$route_parity_dir/boundary.${family}.constructor.routes"
  missing_boundary_theorem_name=$(comm -13 "$route_parity_dir/boundary.theoremName.routes" "$route_parity_dir/boundary.${family}.routes")
  missing_boundary_family=$(comm -23 "$route_parity_dir/boundary.theoremName.routes" "$route_parity_dir/boundary.${family}.routes")
  missing_boundary_constructor=$(comm -23 "$route_parity_dir/boundary.${family}.routes" "$route_parity_dir/boundary.${family}.constructor.routes")

  if [ -n "$missing_boundary_theorem_name" ]; then
    echo "FAIL: semantic boundary-aware $family payload routes without theorem-name payload counterparts"
    printf '%s\n' "$missing_boundary_theorem_name" | sed 's/^/MISSING: /'
    exit 1
  else
    echo "PASS: semantic boundary-aware $family payload routes have theorem-name payload counterparts"
  fi

  if [ -n "$missing_boundary_family" ]; then
    echo "FAIL: semantic boundary-aware theorem-name payload routes without $family payload counterparts"
    printf '%s\n' "$missing_boundary_family" | sed 's/^/MISSING: /'
    exit 1
  else
    echo "PASS: semantic boundary-aware theorem-name payload routes have $family payload counterparts"
  fi

  if [ -n "$missing_boundary_constructor" ]; then
    echo "FAIL: semantic boundary-aware $family payload projection routes without constructor counterparts"
    printf '%s\n' "$missing_boundary_constructor" | sed 's/^/MISSING: /'
    exit 1
  else
    echo "PASS: semantic boundary-aware $family payload projection routes have constructor counterparts"
  fi
done

direct_package_parity_dir=$(mktemp -d "${TMPDIR:-/tmp}/poincare-semantic-direct-package.$$-XXXXXX")
awk '/^theorem / {print $2}' \
  Poincare.lean Poincare/*.lean \
  > "$direct_package_parity_dir/theorems"
sed -n 's/^\(.*\)_to_direct_verification_payload_eq$/\1/p' \
  "$direct_package_parity_dir/theorems" | sort -u \
  > "$direct_package_parity_dir/direct.routes"
sed -n 's/^\(.*\)_to_package_eq$/\1/p' \
  "$direct_package_parity_dir/theorems" | sort -u \
  > "$direct_package_parity_dir/package.routes"
sed -n 's/^\(.*\)_to_statement_eq$/\1/p' \
  "$direct_package_parity_dir/theorems" | sort -u \
  > "$direct_package_parity_dir/statement.routes"

comm -23 "$direct_package_parity_dir/direct.routes" \
    "$direct_package_parity_dir/package.routes" \
  | rg -v '^poincare_(assembly_inputs|target)_payload_of_surgery_and_topology_package_extraction_derivation$' \
    > "$direct_package_parity_dir/missing-package.routes" || true
comm -23 "$direct_package_parity_dir/package.routes" \
    "$direct_package_parity_dir/direct.routes" |
  rg -v '^.*_of_remaining_dependency_and_packaged_(smooth_statement|canonical_smooth_three_sphere_statement|reverse_canonical_smooth_three_sphere_statement)$' \
    > "$direct_package_parity_dir/missing-direct.routes" || true
comm -23 "$direct_package_parity_dir/statement.routes" \
    "$direct_package_parity_dir/package.routes" \
  > "$direct_package_parity_dir/statement-missing-package.routes"
comm -23 "$direct_package_parity_dir/statement.routes" \
    "$direct_package_parity_dir/direct.routes" \
  > "$direct_package_parity_dir/statement-missing-direct.routes"

if [ -s "$direct_package_parity_dir/missing-package.routes" ]; then
  echo "FAIL: semantic direct-verification route aliases without package aliases"
  sed 's/^/MISSING: /' "$direct_package_parity_dir/missing-package.routes"
  exit 1
else
  echo "PASS: semantic direct-verification route aliases have package aliases"
fi

if [ -s "$direct_package_parity_dir/missing-direct.routes" ]; then
  echo "FAIL: semantic package route aliases without direct-verification aliases outside remaining packaged smooth routes"
  sed 's/^/MISSING: /' "$direct_package_parity_dir/missing-direct.routes"
  exit 1
else
  echo "PASS: semantic package route aliases have direct-verification aliases outside remaining packaged smooth routes"
fi

if [ -s "$direct_package_parity_dir/statement-missing-package.routes" ]; then
  echo "FAIL: semantic statement route aliases without package aliases"
  sed 's/^/MISSING: /' "$direct_package_parity_dir/statement-missing-package.routes"
  exit 1
else
  echo "PASS: semantic statement route aliases have package aliases"
fi

if [ -s "$direct_package_parity_dir/statement-missing-direct.routes" ]; then
  echo "FAIL: semantic statement route aliases without direct-verification aliases"
  sed 's/^/MISSING: /' "$direct_package_parity_dir/statement-missing-direct.routes"
  exit 1
else
  echo "PASS: semantic statement route aliases have direct-verification aliases"
fi

check_route_counterpart_family() {
  route_suffix="$1"
  label="$2"
  shift 2
  route_file="$direct_package_parity_dir/${label}.routes"
  missing_file="$direct_package_parity_dir/${label}.missing"
  sed -n "s/^\\(.*\\)${route_suffix}$/\\1/p" \
    "$direct_package_parity_dir/theorems" | sort -u > "$route_file"
  awk -v counterpart_suffixes="$*" '
    BEGIN { suffix_count = split(counterpart_suffixes, suffixes, " ") }
    NR == FNR { names[$0] = 1; next }
    { for (i = 1; i <= suffix_count; i++) {
        target = $0 suffixes[i]
        if (!(target in names)) print target
      }
    }
  ' "$direct_package_parity_dir/theorems" "$route_file" > "$missing_file"
  rg -v 'poincare_conjecture|_of_remaining_dependency_and_packaged_(smooth_statement|canonical_smooth_three_sphere_statement|reverse_canonical_smooth_three_sphere_statement)' \
    "$missing_file" > "$missing_file.nonreserved" || true
  if [ -s "$missing_file.nonreserved" ]; then
    echo "FAIL: semantic ${label} route aliases without required counterparts"
    sed 's/^/MISSING: /' "$missing_file.nonreserved"
    exit 1
  else
    echo "PASS: semantic ${label} route aliases have required counterparts"
  fi
}

check_route_base_endpoint_family() {
  route_suffix="$1"
  label="$2"
  route_file="$direct_package_parity_dir/${label}.base-routes"
  missing_file="$direct_package_parity_dir/${label}.base-missing"
  sed -n "s/^\\(.*${route_suffix%_eq}\\)_eq$/\\1/p" \
    "$direct_package_parity_dir/theorems" | sort -u > "$route_file"
  awk '
    NR == FNR { names[$0] = 1; next }
    !($0 in names) { print }
  ' "$direct_package_parity_dir/theorems" "$route_file" > "$missing_file"
  rg -v 'poincare_conjecture|_of_remaining_dependency_and_packaged_(smooth_statement|canonical_smooth_three_sphere_statement|reverse_canonical_smooth_three_sphere_statement)' \
    "$missing_file" > "$missing_file.nonreserved" || true
  if [ -s "$missing_file.nonreserved" ]; then
    echo "FAIL: semantic ${label} route equality contracts without direct endpoint names"
    sed 's/^/MISSING: /' "$missing_file.nonreserved"
    exit 1
  else
    echo "PASS: semantic ${label} route equality contracts expose direct endpoint names"
  fi
}

check_route_base_endpoint_prefix() {
  route_suffix="$1"
  route_prefix="$2"
  label="$3"
  route_base="${route_prefix}${route_suffix%_eq}"
  route_name="${route_base}_eq"
  if rg -qx "$route_name" "$direct_package_parity_dir/theorems" &&
      ! rg -qx "$route_base" "$direct_package_parity_dir/theorems"; then
    echo "FAIL: semantic ${label} route equality contract without direct endpoint name"
    echo "MISSING: ${route_base}"
    exit 1
  fi
}

check_route_counterpart_family '_to_finite_extinction_eq' finite-extinction \
  _to_package_eq _to_direct_verification_payload_eq
check_route_counterpart_family '_to_boundary_route_eq' boundary \
  _to_package_eq _to_direct_verification_payload_eq _to_finite_extinction_eq
check_route_counterpart_family '_to_lifted_route_eq' lifted \
  _to_package_eq _to_direct_verification_payload_eq _to_finite_extinction_eq _to_boundary_route_eq
check_route_counterpart_family '_to_extraction_derivation_eq' extraction-derivation \
  _to_statement_eq _to_finite_extinction_eq _to_package_eq _to_direct_verification_payload_eq
check_route_counterpart_family '_to_remaining_dependency_eq' remaining-dependency \
  _to_package_eq _to_direct_verification_payload_eq _to_finite_extinction_eq
check_route_counterpart_family '_to_forgetful_dependencies_eq' forgetful-dependencies \
  _to_package_eq _to_direct_verification_payload_eq _to_finite_extinction_eq
check_route_counterpart_family '_to_boundary_certificate_eq' boundary-certificate \
  _to_package_eq _to_direct_verification_payload_eq _to_finite_extinction_eq _to_remaining_dependency_eq
check_route_counterpart_family '_to_projected_dependency_eq' projected-dependency \
  _to_package_eq _to_direct_verification_payload_eq _to_finite_extinction_eq
check_route_base_endpoint_family '_to_projected_dependency_eq' projected-dependency
for route_suffix in \
  _to_direct_verification_payload_eq \
  _to_remaining_dependency_eq \
  _to_boundary_certificate_eq \
  _to_surgery_derivative_payload_eq \
  _to_pointwise_equation_payload_eq \
  _to_direct_pointwise_equation_payload_eq \
  _to_analytic_boundary_eq \
  _to_derivation_and_boundary_payload_eq \
  _to_finite_extinction_eq \
  _to_package_eq
do
  check_route_base_endpoint_prefix "$route_suffix" \
    'analytic_foundation_with_equation_boundary_statements_of_completion_certificate_with_equation_boundary_verification_payload' \
    'CompletionTarget boundary-aware analytic-foundation certificate route'
done
echo "PASS: semantic CompletionTarget boundary-aware analytic-foundation certificate route equality contracts expose direct endpoint names"
for route_suffix in \
  _to_direct_verification_payload_eq \
  _to_remaining_dependency_eq \
  _to_boundary_certificate_eq \
  _to_analytic_boundary_eq \
  _to_derivation_and_boundary_payload_eq \
  _to_pointwise_equation_payload_eq \
  _to_direct_pointwise_equation_payload_eq \
  _to_finite_extinction_eq \
  _to_package_eq
do
  check_route_base_endpoint_prefix "$route_suffix" \
    'analytic_derivation_and_boundary_payload_statements_of_completion_certificate_with_equation_boundary_verification_payload' \
    'CompletionTarget boundary-aware analytic derivation-boundary payload certificate route'
done
echo "PASS: semantic CompletionTarget boundary-aware analytic derivation-boundary payload certificate route equality contracts expose direct endpoint names"
for route_suffix in \
  _to_direct_verification_payload_eq \
  _to_remaining_dependency_eq \
  _to_boundary_certificate_eq \
  _to_analytic_boundary_eq \
  _to_derivation_and_boundary_payload_eq \
  _to_pointwise_equation_payload_eq \
  _to_direct_pointwise_equation_payload_eq \
  _to_finite_extinction_eq \
  _to_package_eq
do
  check_route_base_endpoint_prefix "$route_suffix" \
    'analytic_derivation_statements_of_completion_certificate_with_equation_boundary_verification_payload' \
    'CompletionTarget boundary-aware analytic derivation certificate route'
done
echo "PASS: semantic CompletionTarget boundary-aware analytic derivation certificate route equality contracts expose direct endpoint names"
for route_suffix in \
  _to_direct_verification_payload_eq \
  _to_projected_dependency_eq \
  _to_remaining_dependency_eq \
  _to_equation_boundary_remaining_dependency_eq \
  _to_boundary_certificate_eq \
  _to_pointwise_equation_payload_eq \
  _to_derivative_payload_eq \
  _to_direct_pointwise_equation_payload_eq \
  _to_analytic_boundary_eq \
  _to_derivation_and_boundary_payload_eq \
  _to_surgery_derivative_payload_eq \
  _to_boundary_payload_eq \
  _to_finite_extinction_eq \
  _to_package_eq
do
  check_route_base_endpoint_prefix "$route_suffix" \
    'finite_extinction_of_completion_certificate_with_equation_boundary_verification_payload' \
    'CompletionTarget boundary-aware finite-extinction certificate route'
done
echo "PASS: semantic CompletionTarget boundary-aware finite-extinction certificate route equality contracts expose direct endpoint names"

for route_prefix in \
  canonical_completion_criterion_of_completion_certificate_with_equation_boundary_verification_payload_to_boundary_certificate \
  canonical_completion_criterion_of_completion_certificate_with_equation_boundary_verification_payload_to_direct_verification_payload \
  canonical_completion_criterion_of_completion_certificate_with_equation_boundary_verification_payload_to_finite_extinction \
  canonical_completion_criterion_of_completion_certificate_with_equation_boundary_verification_payload_to_package \
  canonical_completion_criterion_of_completion_certificate_with_equation_boundary_verification_payload_to_project_criterion \
  canonical_completion_criterion_of_completion_certificate_with_equation_boundary_verification_payload_to_remaining_dependency \
  canonical_completion_criterion_of_completion_certificate_with_equation_boundary_verification_payload_to_target_statement \
  canonical_completion_payload_of_completion_certificate_with_equation_boundary_verification_payload_to_boundary_certificate \
  canonical_completion_payload_of_completion_certificate_with_equation_boundary_verification_payload_to_direct_verification_payload \
  canonical_completion_payload_of_completion_certificate_with_equation_boundary_verification_payload_to_finite_extinction \
  canonical_completion_payload_of_completion_certificate_with_equation_boundary_verification_payload_to_package \
  canonical_completion_payload_of_completion_certificate_with_equation_boundary_verification_payload_to_project_payload \
  canonical_completion_payload_of_completion_certificate_with_equation_boundary_verification_payload_to_remaining_dependency \
  canonical_completion_payload_of_completion_certificate_with_equation_boundary_verification_payload_to_target_statement \
  canonical_completion_target_of_completion_certificate_with_equation_boundary_verification_payload_to_boundary_certificate \
  canonical_completion_target_of_completion_certificate_with_equation_boundary_verification_payload_to_direct_verification_payload \
  canonical_completion_target_of_completion_certificate_with_equation_boundary_verification_payload_to_finite_extinction \
  canonical_completion_target_of_completion_certificate_with_equation_boundary_verification_payload_to_package \
  canonical_completion_target_of_completion_certificate_with_equation_boundary_verification_payload_to_poincare_conjecture \
  canonical_completion_target_of_completion_certificate_with_equation_boundary_verification_payload_to_remaining_dependency \
  canonical_completion_target_of_completion_certificate_with_equation_boundary_verification_payload_to_target_statement \
  completion_criterion_of_completion_certificate_with_equation_boundary_verification_payload_to_boundary_certificate \
  completion_criterion_of_completion_certificate_with_equation_boundary_verification_payload_to_direct_verification_payload \
  completion_criterion_of_completion_certificate_with_equation_boundary_verification_payload_to_finite_extinction \
  completion_criterion_of_completion_certificate_with_equation_boundary_verification_payload_to_package \
  completion_criterion_of_completion_certificate_with_equation_boundary_verification_payload_to_remaining_dependency \
  completion_criterion_of_completion_certificate_with_equation_boundary_verification_payload_to_target_statement \
  poincare_completion_payload_of_completion_certificate_with_equation_boundary_verification_payload_to_boundary_certificate \
  poincare_completion_payload_of_completion_certificate_with_equation_boundary_verification_payload_to_canonical_payload \
  poincare_completion_payload_of_completion_certificate_with_equation_boundary_verification_payload_to_direct_verification_payload \
  poincare_completion_payload_of_completion_certificate_with_equation_boundary_verification_payload_to_finite_extinction \
  poincare_completion_payload_of_completion_certificate_with_equation_boundary_verification_payload_to_package \
  poincare_completion_payload_of_completion_certificate_with_equation_boundary_verification_payload_to_poincare_conjecture_payload \
  poincare_completion_payload_of_completion_certificate_with_equation_boundary_verification_payload_to_remaining_dependency \
  poincare_completion_payload_of_completion_certificate_with_equation_boundary_verification_payload_to_target_statement \
  poincare_conjecture_of_completion_certificate_with_equation_boundary_verification_payload_to_boundary_certificate \
  poincare_conjecture_of_completion_certificate_with_equation_boundary_verification_payload_to_canonical_target \
  poincare_conjecture_of_completion_certificate_with_equation_boundary_verification_payload_to_direct_verification_payload \
  poincare_conjecture_of_completion_certificate_with_equation_boundary_verification_payload_to_finite_extinction \
  poincare_conjecture_of_completion_certificate_with_equation_boundary_verification_payload_to_package \
  poincare_conjecture_of_completion_certificate_with_equation_boundary_verification_payload_to_remaining_dependency \
  poincare_conjecture_of_completion_certificate_with_equation_boundary_verification_payload_to_target_statement \
  poincare_conjecture_payload_of_completion_certificate_with_equation_boundary_verification_payload_to_boundary_certificate \
  poincare_conjecture_payload_of_completion_certificate_with_equation_boundary_verification_payload_to_direct_verification_payload \
  poincare_conjecture_payload_of_completion_certificate_with_equation_boundary_verification_payload_to_finite_extinction \
  poincare_conjecture_payload_of_completion_certificate_with_equation_boundary_verification_payload_to_package \
  poincare_conjecture_payload_of_completion_certificate_with_equation_boundary_verification_payload_to_project_payload \
  poincare_conjecture_payload_of_completion_certificate_with_equation_boundary_verification_payload_to_remaining_dependency \
  target_statement_of_completion_certificate_with_equation_boundary_verification_payload_to_boundary_certificate \
  target_statement_of_completion_certificate_with_equation_boundary_verification_payload_to_canonical_target \
  target_statement_of_completion_certificate_with_equation_boundary_verification_payload_to_direct_verification_payload \
  target_statement_of_completion_certificate_with_equation_boundary_verification_payload_to_finite_extinction \
  target_statement_of_completion_certificate_with_equation_boundary_verification_payload_to_package \
  target_statement_of_completion_certificate_with_equation_boundary_verification_payload_to_poincare_conjecture \
  target_statement_of_completion_certificate_with_equation_boundary_verification_payload_to_remaining_dependency
do
  check_route_base_endpoint_prefix "_eq" "$route_prefix" \
    "CompletionTarget top-level boundary-aware completion-certificate projection route"
done
echo "PASS: CompletionTarget top-level boundary-aware completion-certificate projection route equality contracts expose direct endpoint names"

for route_prefix in \
  completion_certificate_of_literal_payload_of_completion_certificate_with_equation_boundary_verification_payload \
  completion_certificate_of_aggregate_dependency_payload_of_completion_certificate_with_equation_boundary_verification_payload \
  completion_certificate_of_project_statement_payload_of_completion_certificate_with_equation_boundary_verification_payload
do
  check_route_base_endpoint_prefix "_eq" "$route_prefix" \
    "CompletionTarget boundary-aware checked-certificate payload projection route"
done
  echo "PASS: CompletionTarget boundary-aware checked-certificate payload projection route equality contracts expose direct endpoint names"

  for route_prefix in \
    poincareCompletionCertificate_literal_payload_of_completion_certificate_of_literal_payload \
    poincareCompletionCertificate_theoremName_payload_of_completion_certificate_of_literal_payload \
    completion_certificate_of_literal_payload_of_completion_certificate
  do
    check_route_base_endpoint_prefix "_eq" "$route_prefix" \
      "CompletionTarget literal-payload checked-certificate bootstrap route"
  done
  echo "PASS: CompletionTarget literal-payload checked-certificate bootstrap route equality contracts expose direct endpoint names"

  for route_prefix in \
    completion_certificate_of_remaining_dependency_and_poincare_payload_of_completion_certificate \
    completion_certificate_of_remaining_dependency_and_canonical_payload_of_completion_certificate \
    completion_certificate_of_remaining_dependency_and_target_statement_of_completion_certificate \
    completion_certificate_of_remaining_dependency_and_canonical_target_of_completion_certificate \
    completion_certificate_of_remaining_dependency_and_completion_criterion_of_completion_certificate
  do
    check_route_base_endpoint_prefix "_eq" "$route_prefix" \
      "CompletionTarget remaining-dependency checked-certificate field reconstruction route"
  done
  echo "PASS: CompletionTarget remaining-dependency checked-certificate field reconstruction route equality contracts expose direct endpoint names"

  for route_suffix in \
    _to_finite_extinction_eq \
    _to_package_eq \
    _to_direct_verification_payload_eq \
    _to_boundary_route_eq \
    _to_remaining_dependency_eq
  do
    check_route_base_endpoint_prefix "$route_suffix" \
      "completion_certificate_of_equation_boundary_remaining_dependency_package" \
      "CompletionTarget strengthened remaining-package checked-certificate route"
  done
  echo "PASS: CompletionTarget strengthened remaining-package checked-certificate route equality contracts expose direct endpoint names"

  for route_suffix in \
    _to_component_requirements_eq \
    _to_package_layer_requirements_eq \
    _to_milestone_requirements_eq \
    _to_component_extraction_derivation_requirements_eq \
    _to_package_layer_extraction_derivation_requirements_eq \
    _to_milestone_extraction_derivation_requirements_eq \
    _to_aggregate_extraction_derivation_dependencies_eq \
    _to_dependency_projections_eq \
    _to_extraction_derivation_dependency_projections_eq \
    _to_lifted_homeomorphism_derivation_dependency_projections_eq \
    _to_forgetful_dependencies_eq
  do
    check_route_base_endpoint_prefix "$route_suffix" \
      "completion_certificate_of_equation_boundary_remaining_dependency_package" \
      "CompletionTarget strengthened remaining-package requirement/projection checked-certificate route"
  done
  echo "PASS: CompletionTarget strengthened remaining-package requirement/projection checked-certificate route equality contracts expose direct endpoint names"

  for route_suffix in \
    _to_remaining_dependency_eq \
    _to_dependency_projections_eq \
    _to_extraction_derivation_dependency_projections_eq \
    _to_finite_extinction_eq \
    _to_package_eq \
    _to_direct_verification_payload_eq \
    _to_forgetful_dependencies_eq
  do
    check_route_base_endpoint_prefix "$route_suffix" \
      "completion_certificate_of_component_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package" \
      "CompletionTarget strengthened remaining-package component-requirements payload checked-certificate route"
  done
  echo "PASS: CompletionTarget strengthened remaining-package component-requirements payload checked-certificate route equality contracts expose direct endpoint names"

  for route_suffix in \
    _to_remaining_dependency_eq \
    _to_dependency_projections_eq \
    _to_extraction_derivation_dependency_projections_eq \
    _to_finite_extinction_eq \
    _to_package_eq \
    _to_direct_verification_payload_eq \
    _to_forgetful_dependencies_eq
  do
    check_route_base_endpoint_prefix "$route_suffix" \
      "completion_certificate_of_package_layer_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package" \
      "CompletionTarget strengthened remaining-package package-layer requirements payload checked-certificate route"
  done
  echo "PASS: CompletionTarget strengthened remaining-package package-layer requirements payload checked-certificate route equality contracts expose direct endpoint names"

  for route_suffix in \
    _to_remaining_dependency_eq \
    _to_dependency_projections_eq \
    _to_extraction_derivation_dependency_projections_eq \
    _to_finite_extinction_eq \
    _to_package_eq \
    _to_direct_verification_payload_eq \
    _to_forgetful_dependencies_eq
  do
    check_route_base_endpoint_prefix "$route_suffix" \
      "completion_certificate_of_milestone_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package" \
      "CompletionTarget strengthened remaining-package milestone requirements payload checked-certificate route"
  done
  echo "PASS: CompletionTarget strengthened remaining-package milestone requirements payload checked-certificate route equality contracts expose direct endpoint names"

  for route_suffix in \
    _to_remaining_dependency_eq \
    _to_finite_extinction_eq \
    _to_dependency_projections_eq \
    _to_direct_verification_payload_eq \
    _to_package_eq \
    _to_extraction_derivation_dependency_projections_eq \
    _to_lifted_homeomorphism_derivation_dependency_projections_eq \
    _to_forgetful_dependencies_eq
  do
    check_route_base_endpoint_prefix "$route_suffix" \
      "completion_certificate_of_component_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package_and_boundary_target_payload" \
      "CompletionTarget strengthened remaining-package boundary-target component-requirements payload checked-certificate route"
  done
  echo "PASS: CompletionTarget strengthened remaining-package boundary-target component-requirements payload checked-certificate route equality contracts expose direct endpoint names"

  for route_suffix in \
    _to_remaining_dependency_eq \
    _to_finite_extinction_eq \
    _to_dependency_projections_eq \
    _to_direct_verification_payload_eq \
    _to_package_eq \
    _to_extraction_derivation_dependency_projections_eq \
    _to_lifted_homeomorphism_derivation_dependency_projections_eq \
    _to_forgetful_dependencies_eq
  do
    check_route_base_endpoint_prefix "$route_suffix" \
      "completion_certificate_of_package_layer_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package_and_boundary_target_payload" \
      "CompletionTarget strengthened remaining-package boundary-target package-layer requirements payload checked-certificate route"
  done
  echo "PASS: CompletionTarget strengthened remaining-package boundary-target package-layer requirements payload checked-certificate route equality contracts expose direct endpoint names"

  for route_suffix in \
    _to_remaining_dependency_eq \
    _to_finite_extinction_eq \
    _to_dependency_projections_eq \
    _to_direct_verification_payload_eq \
    _to_package_eq \
    _to_extraction_derivation_dependency_projections_eq \
    _to_lifted_homeomorphism_derivation_dependency_projections_eq \
    _to_forgetful_dependencies_eq
  do
    check_route_base_endpoint_prefix "$route_suffix" \
      "completion_certificate_of_milestone_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package_and_boundary_target_payload" \
      "CompletionTarget strengthened remaining-package boundary-target milestone requirements payload checked-certificate route"
  done
  echo "PASS: CompletionTarget strengthened remaining-package boundary-target milestone requirements payload checked-certificate route equality contracts expose direct endpoint names"

  for route_suffix in \
    _to_remaining_dependency_eq \
    _to_finite_extinction_eq \
    _to_dependency_projections_eq \
    _to_direct_verification_payload_eq \
    _to_package_eq \
    _to_extraction_derivation_dependency_projections_eq \
    _to_lifted_homeomorphism_derivation_dependency_projections_eq \
    _to_forgetful_dependencies_eq
  do
    check_route_base_endpoint_prefix "$route_suffix" \
      "completion_certificate_of_component_extraction_derivation_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package_and_boundary_target_payload" \
      "CompletionTarget strengthened remaining-package boundary-target component extraction-derivation requirements payload checked-certificate route"
  done
  echo "PASS: CompletionTarget strengthened remaining-package boundary-target component extraction-derivation requirements payload checked-certificate route equality contracts expose direct endpoint names"

  for route_suffix in \
    _to_remaining_dependency_eq \
    _to_finite_extinction_eq \
    _to_dependency_projections_eq \
    _to_direct_verification_payload_eq \
    _to_package_eq \
    _to_extraction_derivation_dependency_projections_eq \
    _to_lifted_homeomorphism_derivation_dependency_projections_eq \
    _to_forgetful_dependencies_eq
  do
    check_route_base_endpoint_prefix "$route_suffix" \
      "completion_certificate_of_package_layer_extraction_derivation_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package_and_boundary_target_payload" \
      "CompletionTarget strengthened remaining-package boundary-target package-layer extraction-derivation requirements payload checked-certificate route"
  done
  echo "PASS: CompletionTarget strengthened remaining-package boundary-target package-layer extraction-derivation requirements payload checked-certificate route equality contracts expose direct endpoint names"

  for route_suffix in \
    _to_remaining_dependency_eq \
    _to_finite_extinction_eq \
    _to_dependency_projections_eq \
    _to_direct_verification_payload_eq \
    _to_package_eq \
    _to_extraction_derivation_dependency_projections_eq \
    _to_lifted_homeomorphism_derivation_dependency_projections_eq \
    _to_forgetful_dependencies_eq
  do
    check_route_base_endpoint_prefix "$route_suffix" \
      "completion_certificate_of_milestone_extraction_derivation_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package_and_boundary_target_payload" \
      "CompletionTarget strengthened remaining-package boundary-target milestone extraction-derivation requirements payload checked-certificate route"
  done
  echo "PASS: CompletionTarget strengthened remaining-package boundary-target milestone extraction-derivation requirements payload checked-certificate route equality contracts expose direct endpoint names"

  for route_suffix in \
    _to_projected_dependency_eq \
    _to_boundary_certificate_eq \
  _to_remaining_dependency_eq \
  _to_finite_extinction_eq \
  _to_package_eq \
  _to_direct_verification_payload_eq
do
  check_route_base_endpoint_prefix "$route_suffix" \
    "poincareCompletionCertificate_theoremName_payload_of_completion_certificate_with_equation_boundary_verification_payload" \
    "CompletionTarget boundary-aware theorem-name constructor payload route"
done
echo "PASS: CompletionTarget boundary-aware theorem-name constructor payload route equality contracts expose direct endpoint names"

for route_suffix in \
  _to_projected_dependency_eq \
  _to_boundary_certificate_eq \
  _to_remaining_dependency_eq \
  _to_finite_extinction_eq \
  _to_package_eq \
  _to_direct_verification_payload_eq
do
  check_route_base_endpoint_prefix "$route_suffix" \
    "poincareCompletionCertificate_literal_payload_of_completion_certificate_with_equation_boundary_verification_payload" \
    "CompletionTarget boundary-aware literal-payload constructor payload route"
done
echo "PASS: CompletionTarget boundary-aware literal-payload constructor payload route equality contracts expose direct endpoint names"

for route_suffix in \
  _to_projected_dependency_eq \
  _to_boundary_certificate_eq \
  _to_remaining_dependency_eq \
  _to_finite_extinction_eq \
  _to_package_eq \
  _to_direct_verification_payload_eq \
  _to_forgetful_dependencies_eq
do
  check_route_base_endpoint_prefix "$route_suffix" \
    "poincareCompletionCertificate_project_statement_payload_of_completion_certificate_with_equation_boundary_verification_payload" \
    "CompletionTarget boundary-aware project-statement constructor payload route"
done
echo "PASS: CompletionTarget boundary-aware project-statement constructor payload route equality contracts expose direct endpoint names"

for route_suffix in \
  _to_projected_dependency_eq \
  _to_boundary_certificate_eq \
  _to_remaining_dependency_eq \
  _to_finite_extinction_eq \
  _to_package_eq \
  _to_direct_verification_payload_eq \
  _to_forgetful_dependencies_eq
do
  check_route_base_endpoint_prefix "$route_suffix" \
    "poincareCompletionCertificate_aggregate_dependency_payload_of_completion_certificate_with_equation_boundary_verification_payload" \
    "CompletionTarget boundary-aware aggregate-dependency constructor payload route"
done
echo "PASS: CompletionTarget boundary-aware aggregate-dependency constructor payload route equality contracts expose direct endpoint names"

for route_suffix in \
  _to_projected_dependency_eq \
  _to_boundary_certificate_eq \
  _to_remaining_dependency_eq \
  _to_finite_extinction_eq \
  _to_package_eq \
  _to_direct_verification_payload_eq
do
  check_route_base_endpoint_prefix "$route_suffix" \
    "completion_certificate_of_literal_payload_of_completion_certificate_with_equation_boundary_verification_payload" \
    "CompletionTarget boundary-aware literal-payload constructor route"
done
echo "PASS: CompletionTarget boundary-aware literal-payload constructor route equality contracts expose direct endpoint names"

for route_suffix in \
  _to_projected_dependency_eq \
  _to_boundary_certificate_eq \
  _to_remaining_dependency_eq \
  _to_finite_extinction_eq \
  _to_package_eq \
  _to_direct_verification_payload_eq \
  _to_forgetful_dependencies_eq
do
  check_route_base_endpoint_prefix "$route_suffix" \
    "completion_certificate_of_project_statement_payload_of_completion_certificate_with_equation_boundary_verification_payload" \
    "CompletionTarget boundary-aware project-statement constructor route"
done
echo "PASS: CompletionTarget boundary-aware project-statement constructor route equality contracts expose direct endpoint names"

for route_suffix in \
  _to_projected_dependency_eq \
  _to_boundary_certificate_eq \
  _to_remaining_dependency_eq \
  _to_finite_extinction_eq \
  _to_package_eq \
  _to_direct_verification_payload_eq \
  _to_forgetful_dependencies_eq
do
  check_route_base_endpoint_prefix "$route_suffix" \
    "completion_certificate_of_aggregate_dependency_payload_of_completion_certificate_with_equation_boundary_verification_payload" \
    "CompletionTarget boundary-aware aggregate-dependency payload constructor route"
done
echo "PASS: CompletionTarget boundary-aware aggregate-dependency payload constructor route equality contracts expose direct endpoint names"

for route_suffix in \
  _to_direct_verification_payload_eq \
  _to_remaining_dependency_eq \
  _to_boundary_certificate_eq \
  _to_analytic_boundary_eq \
  _to_derivation_and_boundary_payload_eq \
  _to_derivative_payload_eq \
  _to_verification_payload_eq \
  _to_pointwise_equation_payload_eq \
  _to_direct_pointwise_equation_payload_eq \
  _to_finite_extinction_eq \
  _to_package_eq
do
  check_route_base_endpoint_prefix "$route_suffix" \
    'equation_boundary_payload_statements_of_completion_certificate_with_equation_boundary_verification_payload' \
    'CompletionTarget boundary-aware equation-boundary payload certificate route'
done
echo "PASS: semantic CompletionTarget boundary-aware equation-boundary payload certificate route equality contracts expose direct endpoint names"
for route_prefix in \
  poincare_assembly_inputs_payload_of_surgery_and_topology_package_extraction_derivation \
  poincare_target_payload_of_surgery_and_topology_package_extraction_derivation \
  poincare_completion_payload_of_surgery_and_topology_package_extraction_derivation \
  poincare_statement_of_surgery_and_topology_package_extraction_derivation \
  canonical_three_sphere_statement_of_surgery_and_topology_package_extraction_derivation
do
  check_route_base_endpoint_prefix '_to_extraction_derivation_eq' "$route_prefix" 'FullAssembly certified extraction derivation'
  check_route_base_endpoint_prefix '_to_statement_eq' "$route_prefix" 'FullAssembly certified extraction statement'
done
echo "PASS: semantic FullAssembly certified extraction route equality contracts expose direct endpoint names"
for route_prefix in \
  poincare_assembly_inputs_payload_of_surgery_and_topology_packages \
  poincare_target_payload_of_surgery_and_topology_packages \
  poincare_completion_payload_of_surgery_and_topology_packages \
  poincare_statement_of_surgery_and_topology_packages \
  canonical_three_sphere_statement_of_surgery_and_topology_packages
do
  check_route_base_endpoint_prefix '_to_extraction_statement_eq' "$route_prefix" 'FullAssembly package extraction statement'
done
echo "PASS: semantic FullAssembly package extraction statement route equality contracts expose direct endpoint names"
for route_prefix in \
  poincare_completion_payload_of_surgery_and_topology_packages_via_extinctionOnePointThreeSpaceRecognitionStatement \
  poincare_statement_of_surgery_and_topology_packages_via_extinctionOnePointThreeSpaceRecognitionStatement
do
  if [ "$route_prefix" = "poincare_completion_payload_of_surgery_and_topology_packages_via_extinctionOnePointThreeSpaceRecognitionStatement" ]; then
    check_route_base_endpoint_prefix '_to_project_payload_eq' "$route_prefix" 'FullAssembly one-point recognition project payload'
  fi
  check_route_base_endpoint_prefix '_to_extraction_statement_eq' "$route_prefix" 'FullAssembly one-point recognition extraction statement'
  check_route_base_endpoint_prefix '_to_package_route_eq' "$route_prefix" 'FullAssembly one-point recognition package route'
done
echo "PASS: semantic FullAssembly one-point recognition project-payload route equality contracts expose direct endpoint names"
echo "PASS: semantic FullAssembly one-point recognition extraction-statement route equality contracts expose direct endpoint names"
echo "PASS: semantic FullAssembly one-point recognition package route equality contracts expose direct endpoint names"
for route_prefix in \
  canonical_completion_payload_of_surgery_and_topology_packages_via_extinctionOnePointThreeSpaceRecognitionStatement \
  canonical_completion_target_of_surgery_and_topology_packages_via_extinctionOnePointThreeSpaceRecognitionStatement \
  canonical_completion_criterion_of_surgery_and_topology_packages_via_extinctionOnePointThreeSpaceRecognitionStatement
do
  case "$route_prefix" in
    canonical_completion_target_of_surgery_and_topology_packages_via_extinctionOnePointThreeSpaceRecognitionStatement)
      check_route_base_endpoint_prefix '_to_project_statement_eq' "$route_prefix" 'CompletionTarget one-point recognition project statement'
      ;;
    *)
      check_route_base_endpoint_prefix '_to_project_payload_eq' "$route_prefix" 'CompletionTarget one-point recognition project payload'
      ;;
  esac
  check_route_base_endpoint_prefix '_to_extraction_statement_eq' "$route_prefix" 'CompletionTarget one-point recognition extraction statement'
  check_route_base_endpoint_prefix '_to_package_route_eq' "$route_prefix" 'CompletionTarget one-point recognition package route'
done
echo "PASS: semantic CompletionTarget one-point recognition project endpoint equality contracts expose direct endpoint names"
echo "PASS: semantic CompletionTarget one-point recognition extraction-statement route equality contracts expose direct endpoint names"
echo "PASS: semantic CompletionTarget one-point recognition package route equality contracts expose direct endpoint names"
for route_prefix in \
  poincare_completion_payload_of_surgery_and_topology_packages \
  poincare_statement_of_surgery_and_topology_packages \
  poincare_statement_of_boundary_surgery_and_topology_packages \
  canonical_three_sphere_statement_of_surgery_and_topology_packages \
  canonical_three_sphere_statement_of_boundary_surgery_and_topology_packages
do
  check_route_base_endpoint_prefix '_to_topology_package_extraction_derivation_eq' "$route_prefix" 'FullAssembly package topology extraction derivation'
done
echo "PASS: semantic FullAssembly package topology extraction-derivation route equality contracts expose direct endpoint names"
for route_prefix in \
  poincare_statement_of_boundary_surgery_and_topology_packages \
  poincare_statement_of_boundary_surgery_and_topology_package_extraction_derivation \
  canonical_three_sphere_statement_of_boundary_surgery_and_topology_package_extraction_derivation
do
  check_route_base_endpoint_prefix '_to_boundary_input_route_eq' "$route_prefix" 'FullAssembly boundary input route'
done
echo "PASS: semantic FullAssembly boundary input route equality contracts expose direct endpoint names"
check_route_base_endpoint_prefix '_to_statement_eq' 'extinction_implies_sphere_of_topology_package' 'topology-package statement'
echo "PASS: semantic topology-package statement route equality contract exposes direct endpoint name"
check_route_base_endpoint_prefix '_to_extraction_statement_projections_eq' 'topology_extraction_statement_payload_of_topology_package' 'topology-package extraction-statement projections'
check_route_base_endpoint_prefix '_to_extraction_statement_payload_eq' 'topology_extraction_statement_payload_of_topology_package' 'topology-package extraction-statement payload'
check_route_base_endpoint_prefix '_to_lifted_derivation_projections_eq' 'topology_extraction_statement_payload_of_extraction_statement' 'topology extraction-statement lifted derivation projections'
check_route_base_endpoint_prefix '_to_lifted_derivation_projections_eq' 'topology_extraction_statement_payload_of_topology_package' 'topology-package lifted derivation projections'
echo "PASS: semantic topology-package extraction statement payload route equality contracts expose direct endpoint names"
check_route_base_endpoint_prefix '_to_bridge_payload_eq' 'smoothability_subobligations_of_smoothability_package' 'smoothability subobligations bridge payload'
echo "PASS: semantic smoothability subobligation bridge payload route equality contract exposes direct endpoint name"
for route_prefix in \
  poincare_statement_of_finite_extinction \
  poincare_statement_of_universalFiniteExtinctionStatement
do
  check_route_base_endpoint_prefix '_to_reserved_endpoint_eq' "$route_prefix" 'RicciFlowInterface reserved endpoint'
done
for route_prefix in \
  universalFiniteExtinctionStatement_completion_payload \
  poincare_payload_of_extinction_and_extraction \
  poincare_payload_of_finite_extinction \
  poincare_payload_of_universalFiniteExtinctionStatement
do
  check_route_base_endpoint_prefix '_to_reserved_payload_eq' "$route_prefix" 'RicciFlowInterface reserved payload'
done
echo "PASS: semantic RicciFlowInterface reserved route equality contracts expose direct endpoint names"

echo "SEMANTIC SURFACE: conditional theorem types, projection lemmas, target contracts, mathlib-shaped adapters, adapter-target/project-target statements, blocker/project-target endpoints, blocker adapter nonempty/full-ledger characterizations, whole-ledger/package-layer/component-slot blocker characterizations, adapter-to-whole-image, whole-ledger-to-image, blocker milestone/package/component image iff bridges, package-to-component image bridges, blocker requirement witness routes, ordinary and strengthened component-slot witness bridges, ordinary and strengthened universal blocker discharge routes, component/package/milestone payload bridges, and ledger crosswalk/package-layer/component-slot/milestone-requirement route check"

rm -rf "$check_dir"
check_dir=
check_file=
