# S1287: SourceHDDReadout assembly from S1262/S1275/actualSHEOutput

Date: 2026-10-30. Actual fields assembled; exact first field recorded.
No change to localize_hdd_compat / iplsheapt.

## Actual fields assembled (S1287, EXIT=0)

For arbitrary I : Input Label Choice:

* s1287HDDLocalLattice := s1262HDDLocalLattice (actual rank-one HDD local
  lattice: span of the actual unit-section localization in the completed
  local field);
* s1287SHELocalization := s1275SHELocalization (actual localization
  expression of the actual Theorem 3.11 output);
* s1287SHEOutput := actualSHEOutput I (actual output, bundle, readingMap,
  localization factorization, output/quotient/part equalities);
* s1287Readout := (actualSHEOutput I).readingMap (actual reading map).

The structure S1287ActualHDDReadoutFields packages these four actual fields;
rfl projection lemmas are proved:
  s1287ActualHDDReadoutFields_hddLocalLattice
  s1287ActualHDDReadoutFields_sheLocalization
  s1287ActualHDDReadoutFields_sheOutput
  s1287ActualHDDReadoutFields_readout

No weak Prop/Nonempty gate/arbitrary Set.

## Exact first field

For the SourceSHEHDDCompatibility / HDD-readout joint, after the actual
hddLocalLattice and sheLocalization the first missing field is

  localizeSection :
    forall v o, hddLocalLattice.lattice o v ->
      (actualSHEOutput I).bundle.total

There is no actual map from HDD local-lattice elements (submodule of the
completed local field) to the integral line bundle total.  Consequently
localize_hdd_compat cannot be inhabited either; it is kept as the existing
exact field and not modified (per instruction, iplsheapt localize_hdd_compat
untouched).

The actual readout_reference_compat is available from S1275:
  sheLocalization.expression v o = actualSHEOutput.readingMap v o
(rfl), and indeterminacy_sync is rfl.

For the full dsc->hull+det SourceHDDReadout target, the dsc/H2FProcession and
hull/det fields are not part of this assembly (S1165 exact dsc first gap);
this file supplies the actual HDD-local-lattice/SHE/readout side.

## Consumer

SourceHDDReadout (dsc -> hull + det) and Step 3.11.5 SHE readout; the
assembled actual fields remove the HDD local lattice, SHE localization and
readout requirements.  localizeSection remains the exact first field.

No new weak wrapper.
