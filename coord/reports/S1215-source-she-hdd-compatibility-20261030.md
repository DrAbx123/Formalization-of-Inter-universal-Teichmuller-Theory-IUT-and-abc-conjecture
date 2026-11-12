# S1215: SourceSHEHDDCompatibility exact target structure

Date: 2026-10-30
Lean: tmp/sheaf/xif/paper/S1215SourceSHEHDDCompatibilityActual.lean — EXIT=0.

## Actual donors used

SHEOutputActual: actualSHEOutput I, oneColumnStructure, bundle/localization, readingMap, unitSection, isLocalizationReading, output part/source/quotient equalities.
SourceSharedBoundary/CertificateHullWiring/S1204: J.oneColumnPacket, J.oneColumnScale, J.oneColumnQ, thetaValueAt_eq_oneColumnScale (:366), oneColumnLogReadout_shift.

## Exact target structure

structure S1215HDDLocalLattice (I : Input Label Choice) where
  rank : Nat
  lattice : Theorem311Output I -> (v : FinitePlace Q) -> Set (Fin rank -> oneColumnStructure.localField v)

structure SourceSHEHDDCompatibility (I) (J : OriginalInput l V) where
  hddLocalLattice : S1215HDDLocalLattice I
  sheLocalization : SourceLocalizationExpression oneColumnStructure (Theorem311Output I)
  localizeSection : forall v o, hddLocalLattice.lattice o v -> (actualSHEOutput I).bundle.total
  localize_hdd_compat : forall v o x hx, sheLocalization.expression v o = (actualSHEOutput I).bundle.localization v (localizeSection v o (x,hx))
  readout_reference_compat : forall v o, sheLocalization.expression v o = (actualSHEOutput I).readingMap v o
  logShift_readout_compat : forall m m' j, Real.log (J.oneColumnScale m j) = Real.log (J.oneColumnScale m' j)
  indeterminacy_sync : forall v o, (actualSHEOutput I).readingMap v o = (actualSHEOutput I).bundle.localization v unitSection

No inhabitant of SourceSHEHDDCompatibility is supplied. No weak compatible Prop, True/PUnit, Nonempty gate, or arbitrary Classical.choice is introduced.

## Actual/discharged versus exact

Actual/discharged:
- logShift_readout_compat is the actual S1204 theorem s1215LogShiftReadoutCompat_actual for every J;
- indeterminacy_sync for the actual output is actual s1215IndeterminacySync_actual (rfl through unitSection).

Exact remaining:
- hddLocalLattice: no HDD local lattice/module construction from the actual output;
- localize_hdd_compat: no actual map from HDD lattice elements to the 1-column bundle total with the stated localization equality;
- readout_reference_compat: no actual identification of the arbitrary sheLocalization expression with actualSHEOutput.readingMap;
- sheLocalization: supplied as an exact field, not constructed from the actual HDD output;
- SourceSHESquareSupply S2/G1 source-arrow inhabitants remain open; SourceSHEHDDCompatibility is not asserted inhabited.

## Consumer

Fourth joint consumer path: Step-XI SHE/HDD readout assembly. The exact structure records the HDD local lattice, 1-column localization, readout and indeterminacy data required before any HDD/SHE comparison can be consumed. No HDD readout comparison is claimed.
