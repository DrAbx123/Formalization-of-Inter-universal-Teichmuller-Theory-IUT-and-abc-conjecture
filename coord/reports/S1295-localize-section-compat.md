# S1295: localizeSection / localize_hdd_compat for S1262 lattice

Date: 2026-10-30
Lean: tmp/sheaf/xif/paper/S1295LocalizeSectionSpanActual.lean — EXIT=0.

## Actual

s1295LocalizeSection v o x := s1286LocalizeSection I v o x = unitSection.

s1295LocalizeHDDCompat:
  (s1275SHELocalization I).expression v o =
    (actualSHEOutput I).bundle.localization v (s1295LocalizeSection I v o ⟨x,hx⟩)
actual (rfl via S1286).

This proves the S1215 localize_hdd_compat equation for the S1262 rank-one
lattice with the actual unit section.

## Exact stronger condition

S1295LatticeSectionRepresentation records the stronger requirement that the
section actually represents x under localization:
  localizationInclusion v (bundle.localization v (localizeSection x hx)) = x 0.

No inhabitant is asserted.  A span-induction map from lattice elements to
bundle.total is not available: bundle.total has no localRing-module structure,
and the span generators are completed-integral scalars of the unit section.
The S1215 localize_hdd_compat only requires the expression-side equality,
which is actual with the unit section as above.

No other S1215 field was touched. No weak Prop/Nonempty/True/PUnit/Classical
choice.
