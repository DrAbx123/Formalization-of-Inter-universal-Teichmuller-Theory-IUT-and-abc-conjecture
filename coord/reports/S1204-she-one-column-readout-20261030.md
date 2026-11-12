# S1204: SHE / 1-column log-shift readout audit

Date: 2026-10-30
Read:
- LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceSHETransportConjugation.lean
- tmp/sheaf/xif/paper/SHEOutputActual.lean
- SourceSHEHDDCompatibility.lean: DOES NOT EXIST in tree (planned fourth-joint file)
- LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceSharedBoundary.lean
- LeanFormal/IUT/IUTIII/Corollary312/StepXI/CertificateHullWiring.lean

Lean audit: tmp/sheaf/xif/paper/S1204SHEOneColumnReadoutActual.lean — EXIT=0.

## Actual today

SHEOutputActual:
- actualSHEOutput I : SHEOutputActual I with actual output = theorem311Output I;
- actual bundle integralLineBundle over completionLocalization (completed valuation
  rings of Q);
- readingMap = completed-ring localization of unitSection;
- isLocalizationReading via reading_factorization;
- source/quotient/part_i/part_ii/part_iii equalities actual;
- actualLocalizationExpression and actualOutput_expressible.

SourceSHETransportConjugation:
- actual conjugation of FPrimeStripEquiv representatives (conjugate) with
  toLink coherence;
- actual transport of times-mu actions/layers/unit portions/Kummer and
  evaluation arrows/leg records;
- actual SourceSHESquareSupply.conjugate with field laws, coherent with the
  transport square. This transports the frozen conditional supply; it does
  not construct the S2/G1 source inhabitants.

1-column actual data (SourceSharedBoundary, CertificateHullWiring):
- oneColumnPacket m, oneColumnQ m, oneColumnScale m j;
- oneColumnQ_transport/vertical, oneColumnScale_transport, oneColumnScale_neg_invariant;
- thetaValueAt_eq_oneColumnScale and thetaValueAt_eq_toPositivePacket_scale
  (CertificateHullWiring:366, :373).

New minimal actual readout lemma (S1204):
- oneColumnLogReadout I m j := Real.log (I.oneColumnScale m j);
- oneColumnLogReadout_shift m m' j:
    readout I m j = readout I m' j, from oneColumnScale_transport;
- oneColumnLogReadout_succ: m to m+1 shift;
- oneColumnLogReadout_theta:
    readout I m j = Real.log (I.thetaValueAt m 0 j), from
    thetaValueAt_eq_oneColumnScale;
- oneColumnLogReadout_positivePacket: readout equals log of the positive-packet
    scale, from toPositivePacket_scale;
- oneColumnQ_shift: oneColumnQ m = oneColumnQ (m+1), from oneColumnQ_vertical.

Consumer and reduced prerequisites:
- Consumer: Step-XI hull/readout path via CertificateHullWiring and the
  SHE output record; the same readout is the 1-column input to the planned
  SourceSHEHDDCompatibility.
- The m-dependence for this readout is removed (shift invariance), and the
  source theta value at (m,0) is identified with it; no per-m re-computation
  or extra hypothesis is needed for the readout algebra.
- However this is only the scalar log-scale readout. It does not construct
  the HDD local lattice/module or its determinant/readout compatibility.

## Exact remaining

1. SourceSHEHDDCompatibility.lean is absent. Missing:
   hddLocalLattice, sheLocalization, localize_hdd_compat,
   readout_reference_compat, logShift_readout_compat, indeterminacy_sync.
2. SHEOutputActual exact obligation: no source-level map from arbitrary
   Theorem311Output data to a distinguished arithmetic-vector-bundle section.
   The current reading is the unit-section localization, not that map.
3. SourceSHETransportConjugation is conditional on SourceSHESquareSupply
   inhabitants (S2/G1 source Kummer/evaluation arrows). It does not construct
   the actual HDD/SHE readout, and the two Card-IPL G1 negative results remain.
4. The actual 1-column shift above is scale/readout invariance only; the
   HDD-level logShift/readout compatibility remains exact.

No weak compatible/isActual Prop, Nonempty gate, True/PUnit, or arbitrary
Classical choice was introduced.
