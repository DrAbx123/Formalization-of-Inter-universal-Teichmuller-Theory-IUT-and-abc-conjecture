# S1238: hddLocalLattice exact first field

Date: 2026-10-30
Lean: tmp/sheaf/xif/paper/S1238HDDLocalLatticeExactFirstField.lean — EXIT=0.

## Result

No actual HDD local lattice can be constructed from actualSHEOutput.
actualSHEOutput supplies:
- actual Theorem311Output;
- oneColumnStructure and the actual bundle;
- bundle.localization, readingMap, unitSection, isLocalizationReading;
- output part/source/quotient equalities.

It does not supply:
- an HDD local lattice/module;
- a rank for such a lattice;
- a local-lattice-to-bundle-total map;
- localize_hdd/readout reference compatibility.

Any Set (Fin rank -> localField v) chosen only from the bundle/unit section would
be arbitrary, not HDD-derived, so it is deliberately not introduced.

## Exact first field

The first outstanding field is exactly:

  S1215HDDLocalLattice (I := I)
    rank : Nat
    lattice : Theorem311Output I -> (v : FinitePlace Q) ->
      Set (Fin rank -> oneColumnStructure.localField v)

The file records this exact type as S1238HDDLocalLatticeType and
S1238HDDLocalLatticeRequired; no inhabitant is asserted.

Actual donor facts retained:
- s1238ActualSHEDonor_reading:
    (actualSHEOutput I).readingMap v o =
      (actualSHEOutput I).bundle.localization v unitSection.

## Consumer / reduced prerequisite

Consumer: SourceSHEHDDCompatibility.hddLocalLattice and the later
localize_hdd_compat/readout_reference_compat fields. Until actual HDD lattice
data exists, only the exact first-field type is available; no weak lattice
or fake Set (Fin 0/1 -> localField) is added.
