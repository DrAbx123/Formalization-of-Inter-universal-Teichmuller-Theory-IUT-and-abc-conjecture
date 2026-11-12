# S1275: non-lattice fields of SourceSHEHDDCompatibility

Date: 2026-10-30
Lean: tmp/sheaf/xif/paper/S1275SHEDDNonLatticeFieldsActual.lean — EXIT=0.

## Actual

sheLocalization:
  s1275SHELocalization I := actualLocalizationExpression I :
    SourceLocalizationExpression oneColumnStructure (Theorem311Output I);
  output = theorem311Output I;
  expression v o = integralLineBundle.localization v unitSection.

readout_reference_compat:
  (s1275SHELocalization I).expression v o = (actualSHEOutput I).readingMap v o
  is actual by rfl.

## Exact

localize_hdd_compat is kept exact, parameterized by an already-supplied
HDD local lattice L and section map localizeSection:

  forall v o x hx,
    E.expression v o =
      (actualSHEOutput I).bundle.localization v (localizeSection v o ⟨x,hx⟩).

No HDD lattice is constructed or modified in S1275.

## Related actual (not modified here)

S1262HDDLocalLatticeActual.lean now gives an actual rank-one HDD local lattice:
rank = 1; lattice = span of the localization of the actual unit section in
the completed local field. EXIT=0. S1275 does not depend on or alter it.

No weak Prop, Nonempty gate, True/PUnit, or arbitrary Classical.choice.
