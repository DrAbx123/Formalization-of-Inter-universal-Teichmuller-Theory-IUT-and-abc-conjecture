# S1294: S1262 HDD lattice + S1275 SHE non-lattice consumer audit

Compiled:
- tmp/sheaf/xif/paper/S1262HDDLocalLatticeActual.lean -> EXIT=0
- tmp/sheaf/xif/paper/S1275SHEDDNonLatticeFieldsActual.lean -> EXIT=0
- tmp/sheaf/xif/paper/S1287SourceHDDReadoutAssemblyActual.lean -> EXIT=0

Axioms (#print axioms):
- s1262HDDLocalLattice_rank : [propext, Classical.choice, Quot.sound]
- s1275ReadoutReferenceCompat : [propext, Classical.choice, Quot.sound]
- s1287ActualHDDReadoutFields : [propext, Classical.choice, Quot.sound]

No sorry/axiom/True/PUnit in these files.

## Actual consumer integration (S1287)

S1287 assembles the actual fields available to the SourceSHEHDDCompatibility /
SourceHDDReadout side:

  S1287ActualHDDReadoutFields
    hddLocalLattice  := S1262.s1262HDDLocalLattice
    sheLocalization  := S1275.s1275SHELocalization
    sheOutput        := actualSHEOutput I
    readout          := (actualSHEOutput I).readingMap

with rfl projection theorems. This is the actual consumer assembly for the
HDD lattice + SHE localization/readout donor.

## Exact remaining fields of SourceSHEHDDCompatibility

The full S1215 structure still needs:

  localizeSection :
    forall v o, hddLocalLattice.lattice o v -> (actualSHEOutput I).bundle.total

  localize_hdd_compat :
    forall v o x hx,
      sheLocalization.expression v o =
        (actualSHEOutput I).bundle.localization v (localizeSection v o <x,hx>)

S1275 already defines the exact type S1275LocalizeHDDCompatExactType,
parameterized by an already-supplied localizeSection; it does not construct
that section map. No source construction for localizeSection is present.

Already actual on the SHE side:
- readout_reference_compat (S1275, rfl vs actualSHEOutput.readingMap)
- logShift_readout_compat (S1215 actual oneColumnLogReadout_shift, needs J)
- indeterminacy_sync (S1215 actual rfl)

## SourceHDDReadout

There is no SourceHDDReadout structure in the tree; S1165 only #checks donors.
Thus the concrete consumer currently available is S1215
SourceSHEHDDCompatibility (and S1287 actual-field assembly).

## Verdict

S1262/S1275/S1287 are actual and compile EXIT=0 with the allowed axiom trio and
no sorry. S1287 is the actual consumer assembly. Full SourceSHEHDDCompatibility
remains exact at localizeSection + localize_hdd_compat.
No fake fields and no new wrapper were written in this audit.