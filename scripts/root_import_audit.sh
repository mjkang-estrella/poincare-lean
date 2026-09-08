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

echo "== Root import audit =="

status=0
root_check_dir=
root_check=
theorem_names=
theorem_names_file=
constructor_surface_dir=
payload_route_parity_dir=

cleanup() {
  if [ -n "$root_check_dir" ]; then
    rm -rf "$root_check_dir"
  fi
  if [ -n "$theorem_names_file" ]; then
    rm -f "$theorem_names_file"
  fi
  if [ -n "$constructor_surface_dir" ]; then
    rm -rf "$constructor_surface_dir"
  fi
  if [ -n "$payload_route_parity_dir" ]; then
    rm -rf "$payload_route_parity_dir"
  fi
}

trap cleanup EXIT

theorem_names_file=$(mktemp "${TMPDIR:-/tmp}/poincare-root-theorems.$$-XXXXXX")
awk '/^theorem / {print $2}' Poincare.lean Poincare/*.lean | sort -u > "$theorem_names_file"
theorem_names=$(cat "$theorem_names_file")

# Shared awk library for the route-naming checks. The theorem-name file is
# read twice: the first pass loads the name set, the second pass checks.
route_awk_lib='
function ends_with(n, s) { return length(n) >= length(s) && substr(n, length(n) - length(s) + 1) == s }
function is_general_route_exception(n) {
  return (index(n, "poincare_conjecture") > 0 ||
    ends_with(n, "_of_remaining_dependency_and_packaged_smooth_statement") ||
    index(n, "_of_remaining_dependency_and_packaged_smooth_statement_to_") > 0 ||
    ends_with(n, "_of_remaining_dependency_and_packaged_canonical_smooth_three_sphere_statement") ||
    index(n, "_of_remaining_dependency_and_packaged_canonical_smooth_three_sphere_statement_to_") > 0 ||
    ends_with(n, "_of_remaining_dependency_and_packaged_reverse_canonical_smooth_three_sphere_statement") ||
    index(n, "_of_remaining_dependency_and_packaged_reverse_canonical_smooth_three_sphere_statement_to_") > 0)
}
function has_theorem(t,   i) {
  if (t in names) return 1
  if (t ~ /[.+*?\[(){}|^$\\]/) { for (i = 1; i <= count; i++) if (all[i] ~ ("^" t "$")) return 1 }
  return 0
}
NR == FNR { names[$0] = 1; all[++count] = $0; next }
'

has_theorem() {
  rg -qx "$1" "$theorem_names_file"
}

is_general_route_exception() {
  case "$1" in
    *poincare_conjecture*) return 0 ;;
    *_of_remaining_dependency_and_packaged_smooth_statement) return 0 ;;
    *_of_remaining_dependency_and_packaged_smooth_statement_to_*) return 0 ;;
    *_of_remaining_dependency_and_packaged_canonical_smooth_three_sphere_statement) return 0 ;;
    *_of_remaining_dependency_and_packaged_canonical_smooth_three_sphere_statement_to_*) return 0 ;;
    *_of_remaining_dependency_and_packaged_reverse_canonical_smooth_three_sphere_statement) return 0 ;;
    *_of_remaining_dependency_and_packaged_reverse_canonical_smooth_three_sphere_statement_to_*) return 0 ;;
    *) return 1 ;;
  esac
}

check_route_counterpart() {
  awk -v source_suffix="$1" -v target_suffix="$2" -v label="$3" "$route_awk_lib"'
  { name = $0
    if (!ends_with(name, source_suffix) || is_general_route_exception(name)) next
    target = substr(name, 1, length(name) - length(source_suffix)) target_suffix
    if (!has_theorem(target)) {
      print "FAIL: root import audit route counterpart missing for " label ": " name " lacks " target
      exit 1
    }
  }' "$theorem_names_file" "$theorem_names_file" || exit 1
}

check_route_counterpart "_to_boundary_route_eq" "_to_package_eq" "boundary route package"
check_route_counterpart "_to_boundary_route_eq" "_to_direct_verification_payload_eq" "boundary route direct payload"
check_route_counterpart "_to_boundary_route_eq" "_to_finite_extinction_eq" "boundary route finite extinction"
check_route_counterpart "_to_extraction_derivation_eq" "_to_statement_eq" "extraction derivation statement"
check_route_counterpart "_to_extraction_derivation_eq" "_to_finite_extinction_eq" "extraction derivation finite extinction"
check_route_counterpart "_to_extraction_derivation_eq" "_to_package_eq" "extraction derivation package"
check_route_counterpart "_to_extraction_derivation_eq" "_to_direct_verification_payload_eq" "extraction derivation direct payload"
check_route_counterpart "_to_remaining_dependency_eq" "_to_package_eq" "remaining dependency package"
check_route_counterpart "_to_remaining_dependency_eq" "_to_direct_verification_payload_eq" "remaining dependency direct payload"
check_route_counterpart "_to_remaining_dependency_eq" "_to_finite_extinction_eq" "remaining dependency finite extinction"
check_route_counterpart "_to_forgetful_dependencies_eq" "_to_package_eq" "forgetful dependencies package"
check_route_counterpart "_to_forgetful_dependencies_eq" "_to_direct_verification_payload_eq" "forgetful dependencies direct payload"
check_route_counterpart "_to_forgetful_dependencies_eq" "_to_finite_extinction_eq" "forgetful dependencies finite extinction"
check_route_counterpart "_to_boundary_certificate_eq" "_to_package_eq" "boundary certificate package"
check_route_counterpart "_to_boundary_certificate_eq" "_to_direct_verification_payload_eq" "boundary certificate direct payload"
check_route_counterpart "_to_boundary_certificate_eq" "_to_finite_extinction_eq" "boundary certificate finite extinction"
check_route_counterpart "_to_boundary_certificate_eq" "_to_remaining_dependency_eq" "boundary certificate remaining dependency"
check_route_counterpart "_to_projected_dependency_eq" "_to_package_eq" "projected dependency package"
check_route_counterpart "_to_projected_dependency_eq" "_to_direct_verification_payload_eq" "projected dependency direct payload"
check_route_counterpart "_to_projected_dependency_eq" "_to_finite_extinction_eq" "projected dependency finite extinction"
echo "PASS: generalized route counterparts are present in root import audit surface"

check_route_base_endpoint() {
  awk -v source_suffix="$1" -v label="$2" "$route_awk_lib"'
  { name = $0
    if (!ends_with(name, source_suffix) || is_general_route_exception(name)) next
    base = ends_with(name, "_eq") ? substr(name, 1, length(name) - 3) : name
    if (!has_theorem(base)) {
      print "FAIL: root import audit route base endpoint missing for " label ": " name " lacks " base
      exit 1
    }
  }' "$theorem_names_file" "$theorem_names_file" || exit 1
}

check_route_base_endpoint "_to_projected_dependency_eq" "projected dependency"
echo "PASS: projected-dependency route equality contracts expose direct endpoint names in root import audit surface"

check_route_base_endpoint_for_prefix() {
  awk -v source_suffix="$1" -v name_prefix="$2" -v label="$3" "$route_awk_lib"'
  { name = $0
    if (name != name_prefix source_suffix) next
    base = ends_with(name, "_eq") ? substr(name, 1, length(name) - 3) : name
    if (!has_theorem(base)) {
      print "FAIL: root import audit route base endpoint missing for " label ": " name " lacks " base
      exit 1
    }
  }' "$theorem_names_file" "$theorem_names_file" || exit 1
}

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
  check_route_base_endpoint_for_prefix "$route_suffix" \
    "analytic_foundation_with_equation_boundary_statements_of_completion_certificate_with_equation_boundary_verification_payload" \
    "CompletionTarget boundary-aware analytic-foundation certificate route"
done
echo "PASS: CompletionTarget boundary-aware analytic-foundation certificate route equality contracts expose direct endpoint names in root import audit surface"

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
  check_route_base_endpoint_for_prefix "$route_suffix" \
    "analytic_derivation_and_boundary_payload_statements_of_completion_certificate_with_equation_boundary_verification_payload" \
    "CompletionTarget boundary-aware analytic derivation-boundary payload certificate route"
done
echo "PASS: CompletionTarget boundary-aware analytic derivation-boundary payload certificate route equality contracts expose direct endpoint names in root import audit surface"

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
  check_route_base_endpoint_for_prefix "$route_suffix" \
    "analytic_derivation_statements_of_completion_certificate_with_equation_boundary_verification_payload" \
    "CompletionTarget boundary-aware analytic derivation certificate route"
done
echo "PASS: CompletionTarget boundary-aware analytic derivation certificate route equality contracts expose direct endpoint names in root import audit surface"

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
  check_route_base_endpoint_for_prefix "$route_suffix" \
    "finite_extinction_of_completion_certificate_with_equation_boundary_verification_payload" \
    "CompletionTarget boundary-aware finite-extinction certificate route"
done
echo "PASS: CompletionTarget boundary-aware finite-extinction certificate route equality contracts expose direct endpoint names in root import audit surface"

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
  check_route_base_endpoint_for_prefix "_eq" "$route_prefix" \
    "CompletionTarget top-level boundary-aware completion-certificate projection route"
done
echo "PASS: CompletionTarget top-level boundary-aware completion-certificate projection route equality contracts expose direct endpoint names in root import audit surface"

for route_prefix in \
  completion_certificate_of_literal_payload_of_completion_certificate_with_equation_boundary_verification_payload \
  completion_certificate_of_aggregate_dependency_payload_of_completion_certificate_with_equation_boundary_verification_payload \
  completion_certificate_of_project_statement_payload_of_completion_certificate_with_equation_boundary_verification_payload
do
  check_route_base_endpoint_for_prefix "_eq" "$route_prefix" \
    "CompletionTarget boundary-aware checked-certificate payload projection route"
done
echo "PASS: CompletionTarget boundary-aware checked-certificate payload projection route equality contracts expose direct endpoint names in root import audit surface"

for route_prefix in \
  poincareCompletionCertificate_literal_payload_of_completion_certificate_of_literal_payload \
  poincareCompletionCertificate_theoremName_payload_of_completion_certificate_of_literal_payload \
  completion_certificate_of_literal_payload_of_completion_certificate
do
  check_route_base_endpoint_for_prefix "_eq" "$route_prefix" \
    "CompletionTarget literal-payload checked-certificate bootstrap route"
done
echo "PASS: CompletionTarget literal-payload checked-certificate bootstrap route equality contracts expose direct endpoint names in root import audit surface"

for route_prefix in \
  completion_certificate_of_remaining_dependency_and_poincare_payload_of_completion_certificate \
  completion_certificate_of_remaining_dependency_and_canonical_payload_of_completion_certificate \
  completion_certificate_of_remaining_dependency_and_target_statement_of_completion_certificate \
  completion_certificate_of_remaining_dependency_and_canonical_target_of_completion_certificate \
  completion_certificate_of_remaining_dependency_and_completion_criterion_of_completion_certificate
do
  check_route_base_endpoint_for_prefix "_eq" "$route_prefix" \
    "CompletionTarget remaining-dependency checked-certificate field reconstruction route"
done
echo "PASS: CompletionTarget remaining-dependency checked-certificate field reconstruction route equality contracts expose direct endpoint names in root import audit surface"

for route_suffix in \
  _to_finite_extinction_eq \
  _to_package_eq \
  _to_direct_verification_payload_eq \
  _to_boundary_route_eq \
  _to_remaining_dependency_eq
do
  check_route_base_endpoint_for_prefix "$route_suffix" \
    "completion_certificate_of_equation_boundary_remaining_dependency_package" \
    "CompletionTarget strengthened remaining-package checked-certificate route"
done
echo "PASS: CompletionTarget strengthened remaining-package checked-certificate route equality contracts expose direct endpoint names in root import audit surface"

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
  check_route_base_endpoint_for_prefix "$route_suffix" \
    "completion_certificate_of_equation_boundary_remaining_dependency_package" \
    "CompletionTarget strengthened remaining-package requirement/projection checked-certificate route"
done
echo "PASS: CompletionTarget strengthened remaining-package requirement/projection checked-certificate route equality contracts expose direct endpoint names in root import audit surface"

for route_suffix in \
  _to_remaining_dependency_eq \
  _to_dependency_projections_eq \
  _to_extraction_derivation_dependency_projections_eq \
  _to_finite_extinction_eq \
  _to_package_eq \
  _to_direct_verification_payload_eq \
  _to_forgetful_dependencies_eq
do
  check_route_base_endpoint_for_prefix "$route_suffix" \
    "completion_certificate_of_component_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package" \
    "CompletionTarget strengthened remaining-package component-requirements payload checked-certificate route"
done
echo "PASS: CompletionTarget strengthened remaining-package component-requirements payload checked-certificate route equality contracts expose direct endpoint names in root import audit surface"

for route_suffix in \
  _to_remaining_dependency_eq \
  _to_dependency_projections_eq \
  _to_extraction_derivation_dependency_projections_eq \
  _to_finite_extinction_eq \
  _to_package_eq \
  _to_direct_verification_payload_eq \
  _to_forgetful_dependencies_eq
do
  check_route_base_endpoint_for_prefix "$route_suffix" \
    "completion_certificate_of_package_layer_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package" \
    "CompletionTarget strengthened remaining-package package-layer requirements payload checked-certificate route"
done
echo "PASS: CompletionTarget strengthened remaining-package package-layer requirements payload checked-certificate route equality contracts expose direct endpoint names in root import audit surface"

for route_suffix in \
  _to_remaining_dependency_eq \
  _to_dependency_projections_eq \
  _to_extraction_derivation_dependency_projections_eq \
  _to_finite_extinction_eq \
  _to_package_eq \
  _to_direct_verification_payload_eq \
  _to_forgetful_dependencies_eq
do
  check_route_base_endpoint_for_prefix "$route_suffix" \
    "completion_certificate_of_milestone_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package" \
    "CompletionTarget strengthened remaining-package milestone requirements payload checked-certificate route"
done
echo "PASS: CompletionTarget strengthened remaining-package milestone requirements payload checked-certificate route equality contracts expose direct endpoint names in root import audit surface"

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
  check_route_base_endpoint_for_prefix "$route_suffix" \
    "completion_certificate_of_component_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package_and_boundary_target_payload" \
    "CompletionTarget strengthened remaining-package boundary-target component-requirements payload checked-certificate route"
done
echo "PASS: CompletionTarget strengthened remaining-package boundary-target component-requirements payload checked-certificate route equality contracts expose direct endpoint names in root import audit surface"

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
  check_route_base_endpoint_for_prefix "$route_suffix" \
    "completion_certificate_of_package_layer_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package_and_boundary_target_payload" \
    "CompletionTarget strengthened remaining-package boundary-target package-layer requirements payload checked-certificate route"
done
echo "PASS: CompletionTarget strengthened remaining-package boundary-target package-layer requirements payload checked-certificate route equality contracts expose direct endpoint names in root import audit surface"

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
  check_route_base_endpoint_for_prefix "$route_suffix" \
    "completion_certificate_of_milestone_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package_and_boundary_target_payload" \
    "CompletionTarget strengthened remaining-package boundary-target milestone requirements payload checked-certificate route"
done
echo "PASS: CompletionTarget strengthened remaining-package boundary-target milestone requirements payload checked-certificate route equality contracts expose direct endpoint names in root import audit surface"

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
  check_route_base_endpoint_for_prefix "$route_suffix" \
    "completion_certificate_of_component_extraction_derivation_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package_and_boundary_target_payload" \
    "CompletionTarget strengthened remaining-package boundary-target component extraction-derivation requirements payload checked-certificate route"
done
echo "PASS: CompletionTarget strengthened remaining-package boundary-target component extraction-derivation requirements payload checked-certificate route equality contracts expose direct endpoint names in root import audit surface"

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
  check_route_base_endpoint_for_prefix "$route_suffix" \
    "completion_certificate_of_package_layer_extraction_derivation_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package_and_boundary_target_payload" \
    "CompletionTarget strengthened remaining-package boundary-target package-layer extraction-derivation requirements payload checked-certificate route"
done
echo "PASS: CompletionTarget strengthened remaining-package boundary-target package-layer extraction-derivation requirements payload checked-certificate route equality contracts expose direct endpoint names in root import audit surface"

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
  check_route_base_endpoint_for_prefix "$route_suffix" \
    "completion_certificate_of_milestone_extraction_derivation_requirements_payload_of_completion_certificate_of_equation_boundary_remaining_dependency_package_and_boundary_target_payload" \
    "CompletionTarget strengthened remaining-package boundary-target milestone extraction-derivation requirements payload checked-certificate route"
done
echo "PASS: CompletionTarget strengthened remaining-package boundary-target milestone extraction-derivation requirements payload checked-certificate route equality contracts expose direct endpoint names in root import audit surface"

for route_suffix in \
  _to_projected_dependency_eq \
  _to_boundary_certificate_eq \
  _to_remaining_dependency_eq \
  _to_finite_extinction_eq \
  _to_package_eq \
  _to_direct_verification_payload_eq
do
  check_route_base_endpoint_for_prefix "$route_suffix" \
    "poincareCompletionCertificate_theoremName_payload_of_completion_certificate_with_equation_boundary_verification_payload" \
    "CompletionTarget boundary-aware theorem-name constructor payload route"
done
echo "PASS: CompletionTarget boundary-aware theorem-name constructor payload route equality contracts expose direct endpoint names in root import audit surface"

for route_suffix in \
  _to_projected_dependency_eq \
  _to_boundary_certificate_eq \
  _to_remaining_dependency_eq \
  _to_finite_extinction_eq \
  _to_package_eq \
  _to_direct_verification_payload_eq
do
  check_route_base_endpoint_for_prefix "$route_suffix" \
    "poincareCompletionCertificate_literal_payload_of_completion_certificate_with_equation_boundary_verification_payload" \
    "CompletionTarget boundary-aware literal-payload constructor payload route"
done
echo "PASS: CompletionTarget boundary-aware literal-payload constructor payload route equality contracts expose direct endpoint names in root import audit surface"

for route_suffix in \
  _to_projected_dependency_eq \
  _to_boundary_certificate_eq \
  _to_remaining_dependency_eq \
  _to_finite_extinction_eq \
  _to_package_eq \
  _to_direct_verification_payload_eq \
  _to_forgetful_dependencies_eq
do
  check_route_base_endpoint_for_prefix "$route_suffix" \
    "poincareCompletionCertificate_project_statement_payload_of_completion_certificate_with_equation_boundary_verification_payload" \
    "CompletionTarget boundary-aware project-statement constructor payload route"
done
echo "PASS: CompletionTarget boundary-aware project-statement constructor payload route equality contracts expose direct endpoint names in root import audit surface"

for route_suffix in \
  _to_projected_dependency_eq \
  _to_boundary_certificate_eq \
  _to_remaining_dependency_eq \
  _to_finite_extinction_eq \
  _to_package_eq \
  _to_direct_verification_payload_eq \
  _to_forgetful_dependencies_eq
do
  check_route_base_endpoint_for_prefix "$route_suffix" \
    "poincareCompletionCertificate_aggregate_dependency_payload_of_completion_certificate_with_equation_boundary_verification_payload" \
    "CompletionTarget boundary-aware aggregate-dependency constructor payload route"
done
echo "PASS: CompletionTarget boundary-aware aggregate-dependency constructor payload route equality contracts expose direct endpoint names in root import audit surface"

for route_suffix in \
  _to_projected_dependency_eq \
  _to_boundary_certificate_eq \
  _to_remaining_dependency_eq \
  _to_finite_extinction_eq \
  _to_package_eq \
  _to_direct_verification_payload_eq
do
  check_route_base_endpoint_for_prefix "$route_suffix" \
    "completion_certificate_of_literal_payload_of_completion_certificate_with_equation_boundary_verification_payload" \
    "CompletionTarget boundary-aware literal-payload constructor route"
done
echo "PASS: CompletionTarget boundary-aware literal-payload constructor route equality contracts expose direct endpoint names in root import audit surface"

for route_suffix in \
  _to_projected_dependency_eq \
  _to_boundary_certificate_eq \
  _to_remaining_dependency_eq \
  _to_finite_extinction_eq \
  _to_package_eq \
  _to_direct_verification_payload_eq \
  _to_forgetful_dependencies_eq
do
  check_route_base_endpoint_for_prefix "$route_suffix" \
    "completion_certificate_of_project_statement_payload_of_completion_certificate_with_equation_boundary_verification_payload" \
    "CompletionTarget boundary-aware project-statement constructor route"
done
echo "PASS: CompletionTarget boundary-aware project-statement constructor route equality contracts expose direct endpoint names in root import audit surface"

for route_suffix in \
  _to_projected_dependency_eq \
  _to_boundary_certificate_eq \
  _to_remaining_dependency_eq \
  _to_finite_extinction_eq \
  _to_package_eq \
  _to_direct_verification_payload_eq \
  _to_forgetful_dependencies_eq
do
  check_route_base_endpoint_for_prefix "$route_suffix" \
    "completion_certificate_of_aggregate_dependency_payload_of_completion_certificate_with_equation_boundary_verification_payload" \
    "CompletionTarget boundary-aware aggregate-dependency payload constructor route"
done
echo "PASS: CompletionTarget boundary-aware aggregate-dependency payload constructor route equality contracts expose direct endpoint names in root import audit surface"

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
  check_route_base_endpoint_for_prefix "$route_suffix" \
    "equation_boundary_payload_statements_of_completion_certificate_with_equation_boundary_verification_payload" \
    "CompletionTarget boundary-aware equation-boundary payload certificate route"
done
echo "PASS: CompletionTarget boundary-aware equation-boundary payload certificate route equality contracts expose direct endpoint names in root import audit surface"

for route_prefix in \
  poincare_statement_of_finite_extinction \
  poincare_statement_of_universalFiniteExtinctionStatement
do
  check_route_base_endpoint_for_prefix "_to_reserved_endpoint_eq" "$route_prefix" "RicciFlowInterface reserved endpoint"
done
for route_prefix in \
  universalFiniteExtinctionStatement_completion_payload \
  poincare_payload_of_extinction_and_extraction \
  poincare_payload_of_finite_extinction \
  poincare_payload_of_universalFiniteExtinctionStatement
do
  check_route_base_endpoint_for_prefix "_to_reserved_payload_eq" "$route_prefix" "RicciFlowInterface reserved payload"
done
echo "PASS: RicciFlowInterface reserved route equality contracts expose direct endpoint names in root import audit surface"

for route_prefix in \
  poincare_assembly_inputs_payload_of_surgery_and_topology_package_extraction_derivation \
  poincare_target_payload_of_surgery_and_topology_package_extraction_derivation \
  poincare_completion_payload_of_surgery_and_topology_package_extraction_derivation \
  poincare_statement_of_surgery_and_topology_package_extraction_derivation \
  canonical_three_sphere_statement_of_surgery_and_topology_package_extraction_derivation
do
  check_route_base_endpoint_for_prefix "_to_extraction_derivation_eq" "$route_prefix" "FullAssembly certified extraction derivation"
  check_route_base_endpoint_for_prefix "_to_statement_eq" "$route_prefix" "FullAssembly certified extraction statement"
done
echo "PASS: FullAssembly certified extraction route equality contracts expose direct endpoint names in root import audit surface"
for route_prefix in \
  poincare_assembly_inputs_payload_of_surgery_and_topology_packages \
  poincare_target_payload_of_surgery_and_topology_packages \
  poincare_completion_payload_of_surgery_and_topology_packages \
  poincare_statement_of_surgery_and_topology_packages \
  canonical_three_sphere_statement_of_surgery_and_topology_packages
do
  check_route_base_endpoint_for_prefix "_to_extraction_statement_eq" "$route_prefix" "FullAssembly package extraction statement"
done
echo "PASS: FullAssembly package extraction statement route equality contracts expose direct endpoint names in root import audit surface"
for route_prefix in \
  poincare_completion_payload_of_surgery_and_topology_packages \
  poincare_statement_of_surgery_and_topology_packages \
  poincare_statement_of_boundary_surgery_and_topology_packages \
  canonical_three_sphere_statement_of_surgery_and_topology_packages \
  canonical_three_sphere_statement_of_boundary_surgery_and_topology_packages
do
  check_route_base_endpoint_for_prefix "_to_topology_package_extraction_derivation_eq" "$route_prefix" "FullAssembly package topology extraction derivation"
done
echo "PASS: FullAssembly package topology extraction-derivation route equality contracts expose direct endpoint names in root import audit surface"
for route_prefix in \
  poincare_statement_of_boundary_surgery_and_topology_packages \
  poincare_statement_of_boundary_surgery_and_topology_package_extraction_derivation \
  canonical_three_sphere_statement_of_boundary_surgery_and_topology_package_extraction_derivation
do
  check_route_base_endpoint_for_prefix "_to_boundary_input_route_eq" "$route_prefix" "FullAssembly boundary input route"
done
echo "PASS: FullAssembly boundary input route equality contracts expose direct endpoint names in root import audit surface"
check_route_base_endpoint_for_prefix "_to_statement_eq" "extinction_implies_sphere_of_topology_package" "topology package statement"
echo "PASS: topology-package statement route equality contract exposes direct endpoint name in root import audit surface"
check_route_base_endpoint_for_prefix "_to_extraction_statement_projections_eq" "topology_extraction_statement_payload_of_topology_package" "topology package extraction-statement projections"
check_route_base_endpoint_for_prefix "_to_extraction_statement_payload_eq" "topology_extraction_statement_payload_of_topology_package" "topology package extraction-statement payload"
check_route_base_endpoint_for_prefix "_to_lifted_derivation_projections_eq" "topology_extraction_statement_payload_of_extraction_statement" "topology extraction-statement lifted derivation projections"
check_route_base_endpoint_for_prefix "_to_lifted_derivation_projections_eq" "topology_extraction_statement_payload_of_topology_package" "topology package lifted derivation projections"
echo "PASS: topology-package extraction statement payload route equality contracts expose direct endpoint names in root import audit surface"
check_route_base_endpoint_for_prefix "_to_bridge_payload_eq" "smoothability_subobligations_of_smoothability_package" "smoothability subobligations bridge payload"
echo "PASS: smoothability subobligation bridge payload route equality contract exposes direct endpoint name in root import audit surface"

check_route_suffix_counterpart() {
  awk -v source_suffix="$1" -v target_suffix="$2" -v label="$3" "$route_awk_lib"'
  { name = $0
    if (!ends_with(name, source_suffix) || is_general_route_exception(name)) next
    target = substr(name, 1, length(name) - length(source_suffix)) target_suffix
    if (!has_theorem(target)) {
      print "FAIL: root import audit suffix counterpart missing for " label ": " name " lacks " target
      exit 1
    }
  }' "$theorem_names_file" "$theorem_names_file" || exit 1
}

check_route_suffix_counterpart "_to_direct_verification_payload_eq" "_to_package_eq" "direct-verification package"
check_route_suffix_counterpart "_to_package_eq" "_to_direct_verification_payload_eq" "package direct-verification"
check_route_suffix_counterpart "_to_statement_eq" "_to_package_eq" "statement package"
check_route_suffix_counterpart "_to_statement_eq" "_to_direct_verification_payload_eq" "statement direct-verification"
check_route_suffix_counterpart "_to_finite_extinction_eq" "_to_package_eq" "finite-extinction package"
check_route_suffix_counterpart "_to_finite_extinction_eq" "_to_direct_verification_payload_eq" "finite-extinction direct-verification"
check_route_suffix_counterpart "_to_lifted_route_eq" "_to_package_eq" "lifted route package"
check_route_suffix_counterpart "_to_lifted_route_eq" "_to_direct_verification_payload_eq" "lifted route direct-verification"
check_route_suffix_counterpart "_to_lifted_route_eq" "_to_finite_extinction_eq" "lifted route finite-extinction"
check_route_suffix_counterpart "_to_lifted_route_eq" "_to_boundary_route_eq" "lifted route boundary"
echo "PASS: route suffix counterparts are present in root import audit surface"

check_route_suffix_clique_counterparts() {
  label=$1
  name_pattern=$2
  shift 2
  for source_suffix in "$@"; do
    for target_suffix in "$@"; do
      if [ "$source_suffix" != "$target_suffix" ]; then
        awk -v source_suffix="$source_suffix" -v target_suffix="$target_suffix" \
          -v label="$label" -v name_pattern="$name_pattern" "$route_awk_lib"'
        { name = $0
          if (index(name, name_pattern) != 1 || !ends_with(name, source_suffix) ||
              length(name) < length(name_pattern) + length(source_suffix) ||
              is_general_route_exception(name)) next
          target = substr(name, 1, length(name) - length(source_suffix)) target_suffix
          if (!has_theorem(target)) {
            print "FAIL: root import audit suffix counterpart missing for " label ": " name " lacks " target
            exit 1
          }
        }' "$theorem_names_file" "$theorem_names_file" || exit 1
      fi
    done
  done
}

check_route_suffix_clique_counterparts \
  "equation-boundary payload route cluster" \
  "analytic_derivation_and_boundary_payload_statements_of_completion_certificate_with_equation_boundary_verification_payload" \
  "_to_analytic_boundary_eq" \
  "_to_derivation_and_boundary_payload_eq" \
  "_to_direct_pointwise_equation_payload_eq" \
  "_to_pointwise_equation_payload_eq"
echo "PASS: equation-boundary payload route cluster counterparts are present in root import audit surface"

check_payload_route_parity() {
  family=$1
  theorem_name_routes="$payload_route_parity_dir/theoremName.routes"
  family_routes="$payload_route_parity_dir/${family}.routes"
  constructor_routes="$payload_route_parity_dir/${family}.constructor.routes"
  missing_theorem_name="$payload_route_parity_dir/${family}.missing-theorem-name"
  missing_family="$payload_route_parity_dir/${family}.missing-family"
  missing_constructor="$payload_route_parity_dir/${family}.missing-constructor"

  sed -n 's/^poincareCompletionCertificate_theoremName_payload_of_completion_certificate_of_\(.*\)_eq$/\1/p' \
    "$theorem_names_file" | sort -u > "$theorem_name_routes"
  sed -n "s/^poincareCompletionCertificate_${family}_payload_of_completion_certificate_of_\\(.*\\)_eq$/\\1/p" \
    "$theorem_names_file" | sort -u > "$family_routes"
  {
    sed -n "s/^completion_certificate_of_${family}_payload_of_\\(.*\\)_eq$/\\1/p" \
      "$theorem_names_file"
    sed -n "s/^completion_certificate_of_${family}_payload_of_completion_certificate_of_\\(.*\\)_eq$/\\1/p" \
      "$theorem_names_file"
  } | sort -u > "$constructor_routes"

  comm -13 "$theorem_name_routes" "$family_routes" > "$missing_theorem_name"
  comm -23 "$theorem_name_routes" "$family_routes" > "$missing_family"
  comm -23 "$family_routes" "$constructor_routes" > "$missing_constructor"

  if [ -s "$missing_theorem_name" ]; then
    echo "FAIL: root import audit ${family} payload routes without theorem-name counterparts"
    sed 's/^/MISSING: /' "$missing_theorem_name"
    status=1
  else
    echo "PASS: root import audit ${family} payload routes have theorem-name counterparts"
  fi

  if [ -s "$missing_family" ]; then
    echo "FAIL: root import audit theorem-name payload routes without ${family} counterparts"
    sed 's/^/MISSING: /' "$missing_family"
    status=1
  else
    echo "PASS: root import audit theorem-name payload routes have ${family} counterparts"
  fi

  if [ -s "$missing_constructor" ]; then
    echo "FAIL: root import audit ${family} payload routes without constructor counterparts"
    sed 's/^/MISSING: /' "$missing_constructor"
    status=1
  else
    echo "PASS: root import audit ${family} payload routes have constructor counterparts"
  fi
}

check_boundary_payload_route_parity() {
  family=$1
  theorem_name_routes="$payload_route_parity_dir/boundary.theoremName.routes"
  family_routes="$payload_route_parity_dir/boundary.${family}.routes"
  constructor_routes="$payload_route_parity_dir/boundary.${family}.constructor.routes"
  missing_theorem_name="$payload_route_parity_dir/boundary.${family}.missing-theorem-name"
  missing_family="$payload_route_parity_dir/boundary.${family}.missing-family"
  missing_constructor="$payload_route_parity_dir/boundary.${family}.missing-constructor"

  sed -n 's/^poincareCompletionCertificate_theoremName_payload_of_completion_certificate_with_equation_boundary_verification_payload_of_\(.*\)_eq$/\1/p' \
    "$theorem_names_file" | sort -u > "$theorem_name_routes"
  sed -n "s/^poincareCompletionCertificate_${family}_payload_of_completion_certificate_with_equation_boundary_verification_payload_of_\\(.*\\)_eq$/\\1/p" \
    "$theorem_names_file" | sort -u > "$family_routes"
  {
    sed -n "s/^completion_certificate_of_${family}_payload_of_completion_certificate_with_equation_boundary_verification_payload_of_\\(.*\\)_eq$/\\1/p" \
      "$theorem_names_file"
    sed -n "s/^completion_certificate_of_${family}_payload_of_poincareCompletionCertificate_${family}_payload_of_completion_certificate_with_equation_boundary_verification_payload_of_\\(.*\\)_eq$/\\1/p" \
      "$theorem_names_file"
  } | sort -u > "$constructor_routes"

  comm -13 "$theorem_name_routes" "$family_routes" > "$missing_theorem_name"
  comm -23 "$theorem_name_routes" "$family_routes" > "$missing_family"
  comm -23 "$family_routes" "$constructor_routes" > "$missing_constructor"

  if [ -s "$missing_theorem_name" ]; then
    echo "FAIL: root import audit boundary-aware ${family} payload routes without theorem-name counterparts"
    sed 's/^/MISSING: /' "$missing_theorem_name"
    status=1
  else
    echo "PASS: root import audit boundary-aware ${family} payload routes have theorem-name counterparts"
  fi

  if [ -s "$missing_family" ]; then
    echo "FAIL: root import audit boundary-aware theorem-name payload routes without ${family} counterparts"
    sed 's/^/MISSING: /' "$missing_family"
    status=1
  else
    echo "PASS: root import audit boundary-aware theorem-name payload routes have ${family} counterparts"
  fi

  if [ -s "$missing_constructor" ]; then
    echo "FAIL: root import audit boundary-aware ${family} payload routes without constructor counterparts"
    sed 's/^/MISSING: /' "$missing_constructor"
    status=1
  else
    echo "PASS: root import audit boundary-aware ${family} payload routes have constructor counterparts"
  fi
}

payload_route_parity_dir=$(mktemp -d "${TMPDIR:-/tmp}/poincare-root-payload-route-parity.$$-XXXXXX")
for payload_family in literal canonical_statement aggregate_canonical_statement aggregate_dependency project_statement; do
  check_payload_route_parity "$payload_family"
  check_boundary_payload_route_parity "$payload_family"
done

constructor_surface_dir=$(mktemp -d "${TMPDIR:-/tmp}/poincare-root-constructor-surface.$$-XXXXXX")
ordinary_constructors="$constructor_surface_dir/ordinary-constructors"
boundary_constructors="$constructor_surface_dir/boundary-constructors"
constructor_missing="$constructor_surface_dir/missing"

perl -0ne 'while (/^theorem\s+(completion_certificate_of_[A-Za-z0-9_]+)\b(.*?)(?=^theorem\s+|\z)/msg) { my ($n,$b)=($1,$2); next if $n =~ /_eq$/; next if $n =~ /_of_completion_certificate(?:_|$)/; next unless $b =~ /:\s*PoincareCompletionCertificate\.\{u\}/s; print "$n\n"; }' \
  Poincare/CompletionTarget.lean | sort -u > "$ordinary_constructors"

if [ ! -s "$ordinary_constructors" ]; then
  echo "FAIL: root import audit found no completion certificate constructors"
  status=1
else
  check_constructor_endpoint_family() {
    prefix=$1
    suffix=$2
    label=$3
    : > "$constructor_missing"
    while IFS= read -r constructor; do
      route=${constructor#completion_certificate_of_}
      endpoint="${prefix}${route}${suffix}"
      if ! has_theorem "$endpoint"; then
        echo "$constructor lacks $endpoint" >> "$constructor_missing"
      fi
    done < "$ordinary_constructors"
    if [ -s "$constructor_missing" ]; then
      echo "FAIL: root import audit completion certificate constructors missing ${label}"
      sed 's/^/MISSING: /' "$constructor_missing"
      status=1
    else
      echo "PASS: root import audit completion certificate constructors expose ${label}"
    fi
  }

  check_constructor_endpoint_family "poincare_conjecture_of_completion_certificate_of_" "" "reserved-theorem endpoints"
  check_constructor_endpoint_family "poincare_conjecture_payload_of_completion_certificate_of_" "" "reserved-payload endpoints"
  check_constructor_endpoint_family "target_statement_of_completion_certificate_of_" "" "target-statement endpoints"
  check_constructor_endpoint_family "canonical_completion_payload_of_completion_certificate_of_" "" "canonical-payload endpoints"
  check_constructor_endpoint_family "poincare_completion_payload_of_completion_certificate_of_" "" "project-payload endpoints"
  check_constructor_endpoint_family "canonical_completion_target_of_completion_certificate_of_" "" "canonical-target endpoints"
  check_constructor_endpoint_family "completion_criterion_of_completion_certificate_of_" "" "completion-criterion endpoints"
  check_constructor_endpoint_family "canonical_completion_criterion_of_completion_certificate_of_" "" "canonical-criterion endpoints"
  check_constructor_endpoint_family "poincare_full_assembly_payload_of_completion_certificate_of_" "" "full-assembly endpoints"
  check_constructor_endpoint_family "poincare_full_assembly_payload_of_completion_certificate_extraction_derivation_of_" "" "certified full-assembly endpoints"
  for payload_family in theoremName literal canonical_statement aggregate_canonical_statement aggregate_dependency project_statement; do
    check_constructor_endpoint_family "poincareCompletionCertificate_${payload_family}_payload_of_completion_certificate_of_" "_eq" "${payload_family} payload routes"
  done
fi

perl -0ne 'while (/^theorem\s+(completion_certificate_with_equation_boundary_verification_payload_of_[A-Za-z0-9_]+)\b(.*?)(?=^theorem\s+|\z)/msg) { my ($n,$b)=($1,$2); next if $n =~ /_eq$/; next unless $b =~ /:\s*PoincareCompletionCertificateWithEquationBoundaryVerificationPayload\.\{u\}/s; print "$n\n"; }' \
  Poincare/CompletionTarget.lean Poincare/CanonicalBridges.lean |
  sort -u > "$boundary_constructors"

if [ ! -s "$boundary_constructors" ]; then
  echo "FAIL: root import audit found no boundary-aware completion certificate constructors"
  status=1
else
  check_boundary_constructor_endpoint_family() {
    endpoint_family=$1
    : > "$constructor_missing"
    while IFS= read -r constructor; do
      route=${constructor#completion_certificate_with_equation_boundary_verification_payload_of_}
      endpoint="${endpoint_family}_of_${route}"
      if ! has_theorem "$endpoint"; then
        echo "$constructor lacks $endpoint" >> "$constructor_missing"
      fi
    done < "$boundary_constructors"
    if [ -s "$constructor_missing" ]; then
      echo "FAIL: root import audit boundary-aware constructors missing ${endpoint_family}"
      sed 's/^/MISSING: /' "$constructor_missing"
      status=1
    else
      echo "PASS: root import audit boundary-aware constructors expose ${endpoint_family}"
    fi
  }

  for endpoint_family in \
      poincare_completion_payload_of_completion_certificate_with_equation_boundary_verification_payload \
      target_statement_of_completion_certificate_with_equation_boundary_verification_payload \
      canonical_completion_payload_of_completion_certificate_with_equation_boundary_verification_payload \
      canonical_completion_target_of_completion_certificate_with_equation_boundary_verification_payload \
      poincare_conjecture_of_completion_certificate_with_equation_boundary_verification_payload \
      poincare_conjecture_payload_of_completion_certificate_with_equation_boundary_verification_payload \
      completion_criterion_of_completion_certificate_with_equation_boundary_verification_payload \
      canonical_completion_criterion_of_completion_certificate_with_equation_boundary_verification_payload \
      poincare_full_assembly_payload_of_completion_certificate_with_equation_boundary_verification_payload \
      poincare_full_assembly_payload_of_completion_certificate_with_equation_boundary_verification_payload_extraction_derivation \
      analytic_foundation_with_equation_boundary_statements_of_completion_certificate_with_equation_boundary_verification_payload \
      equation_boundary_payload_statements_of_completion_certificate_with_equation_boundary_verification_payload \
      analytic_derivation_and_boundary_payload_statements_of_completion_certificate_with_equation_boundary_verification_payload \
      analytic_derivation_statements_of_completion_certificate_with_equation_boundary_verification_payload \
      canonical_three_sphere_statement_of_completion_certificate_with_equation_boundary_verification_payload \
      poincareCompletionCertificate_canonical_statement_payload_of_completion_certificate_with_equation_boundary_verification_payload \
      poincareCompletionCertificate_aggregate_canonical_statement_payload_of_completion_certificate_with_equation_boundary_verification_payload; do
    check_boundary_constructor_endpoint_family "$endpoint_family"
  done

  check_boundary_constructor_payload_eq_family() {
    payload_family=$1
    : > "$constructor_missing"
    while IFS= read -r constructor; do
      route=${constructor#completion_certificate_with_equation_boundary_verification_payload_of_}
      endpoint="poincareCompletionCertificate_${payload_family}_payload_of_completion_certificate_with_equation_boundary_verification_payload_of_${route}_eq"
      if ! has_theorem "$endpoint"; then
        echo "$constructor lacks $endpoint" >> "$constructor_missing"
      fi
    done < "$boundary_constructors"
    if [ -s "$constructor_missing" ]; then
      echo "FAIL: root import audit boundary-aware constructors missing ${payload_family} payload equality routes"
      sed 's/^/MISSING: /' "$constructor_missing"
      status=1
    else
      echo "PASS: root import audit boundary-aware constructors expose ${payload_family} payload equality routes"
    fi
  }

  for payload_family in theoremName literal canonical_statement aggregate_canonical_statement aggregate_dependency project_statement; do
    check_boundary_constructor_payload_eq_family "$payload_family"
  done
fi

for file in $(rg --files Poincare | sort); do
  module=${file%.lean}
  module=$(printf '%s\n' "$module" | tr '/' '.')
  if rg -q "^import ${module}$" Poincare.lean; then
    echo "PASS: Poincare.lean imports ${module}"
  else
    echo "FAIL: Poincare.lean does not import ${module}"
    status=1
  fi
done

root_check_dir=$(mktemp -d "${TMPDIR:-/tmp}/poincare-root-import.$$-XXXXXX")
root_check="$root_check_dir/build.log"

if lake build PoincareAudit.Root.Contracts > "$root_check" 2>&1; then
  echo "PASS: Poincare root exposes canonical target contracts, canonical assembly bridges, and projection assembly"
else
  echo "FAIL: Poincare root does not expose canonical target contracts, canonical assembly bridges, and projection assembly"
  cat "$root_check"
  status=1
fi

rm -rf "$root_check_dir"
root_check_dir=
root_check=

exit "$status"
