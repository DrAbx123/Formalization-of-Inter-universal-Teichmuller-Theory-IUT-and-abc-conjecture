# S1931: paper/source-selected arithmetic Haar — signed-average identity and exact first missing

Date: 2026-11-01.  Task: for the paper/source-selected arithmetic Haar
(unit-region normalization, C6 canonical hull, S865 `rootHaarFactor_normPow_actual`,
`arithmeticTupleHullUnitLogVolume`), prove
`HaarSignedAverageProof.SignedUnitFactorThetaComparison`; or give the exact
first missing.  Do not use an arbitrary `mu`, no fake normalization.

## Result (short)

`SignedUnitFactorThetaComparison` at the paper/source-selected Haar is **reduced
to a single, mu-free real equation and that equation is named**; it is not
asserted.  The arbitrary-`mu` normalization freedom of S1916 is **discharged** by
the source unit-region normalization.  What remains is exactly the identification

    Real.log C3.thetaPacket.q
      = - (arithmeticTupleHullUnitLogVolume places tuple * card) / W,

  card = #(SignedLabel l.value),  W = sum_j j^2 over the signed labels,

i.e. the source theta-packet parameter `q` is determined by the actual C6
arithmetic canonical-hull log index.  This is a comparison of two actual numeric
invariants, **not** a normalization and **not** a statement about `mu`.

## What is proved (all kernel-closed)

1. [PROVED] **The source Haar.**  `paperArithmeticHaar places tuple mu :=
   (mu (arithmeticTupleCanonicalUnitReference places tuple))^{-1} • mu` is an
   additive Haar measure (`paperArithmeticHaar_addHaar`), and it satisfies the
   paper's unit-region normalization exactly:
   `paperArithmeticHaar unitReference = 1` (`paperArithmeticHaar_unitReference`).
   No hull property is used in the normalization.

2. [PROVED] **The source-Haar reduction (the answer to "no arbitrary mu").**
   At this Haar the target identity is *equivalent* to the mu-free equation

     `SourceHaarHullThetaComparison`:
       arithmeticTupleHullUnitLogVolume places tuple
         = (c3ThetaSignedProcession C3).average

   (`paperArithmeticHaar_signedUnitFactor_iff`), hence it is independent of the
   auxiliary additive Haar measure used to build the source Haar
   (`sourceHaar_comparison_independent_of_initialHaar`).  The named missing is
   `S1931FirstMissing := SourceHaarHullThetaComparison`, and
   `s1931_firstMissing_iff_comparison` says it is literally the target at the
   source Haar.

3. [PROVED] **C6 canonical-hull mass at the source Haar.**
   `(paperArithmeticHaar mu (arithmeticTupleCanonicalHull places tuple)).toReal =
   Real.exp (arithmeticTupleHullUnitLogVolume places tuple)`
   (`paperArithmeticHaar_hull_mass`), and for every `a`,
   `paperArithmeticHaar mu hull = ofReal (exp a) ↔ hullUnitLogVolume = a`
   (`paperArithmeticHaar_hull_measure_eq_iff`).  Hence the target is also exactly
   the C6 hull-mass statement `hull mass = ofReal (exp (signed average))`
   (`paperArithmeticHaar_comparison_iff_hull_mass`).

4. [PROVED] **Hull side = norm-power (C6 analogue of S865).**  For an actual
   field-product decomposition `e`, the canonical hull is a least `lambda*O`
   region, and

     `arithmeticTupleHullUnitLogVolume places tuple
        = Real.log (distribHaarChar ((j:J) -> E j) (scalingUnits lam hlam) : Real)`

   for the least scaling vector `lam`
   (`arithmeticTupleHullUnitLogVolume_eq_log_distribHaarChar`).

5. [PROVED] **Theta side = Gaussian q-power.**  With
   `sourceThetaWeightSum l = sum_j ((gaussExponent j.1).toNat : Real)`:
   `sourceThetaWeightSum_pos` (the label 1 contributes 1),
   `thetaPacket_logVolume_eq` (`logVolume = W * log q`), and

     `(c3ThetaSignedProcession C3).average
        = - (Real.log q * W) / card`   (`signedAverage_eq_neg`).

6. [PROVED] **Exact first missing** (`s1931FirstMissing_logq`):
   `S1931FirstMissing ↔ log q = - (hullUnitLogVolume * card)/W`.

7. [PROVED] **Sharpness of the missing.**
   * satisfiable by exactly one packet parameter
     (`sourceHaar_comparison_packet_exists`, `sourceHaar_comparison_packet_unique`);
   * it forces `q <= 1` since `arithmeticTupleHullUnitLogVolume >= 0`, so it
     **fails for every packet with q > 1**
     (`sourceHaar_comparison_forces_q_le_one`,
     `sourceHaar_comparison_false_of_one_lt_q`) — it is not derivable from the
     source normalization alone;
   * at the trivial packet `q = 1` it holds iff the C6 canonical hull and the
     canonical unit reference have the same Haar mass
     (`sourceHaar_comparison_at_one_iff_hull_measure_eq`, via
     `hullUnitLogVolume_eq_zero_iff_measure_eq`).

8. [PROVED] **Constructive direction** (consumer-facing): from the explicit
   source-q identification,
   `signedUnitFactor_of_sourceQ` gives the target at the source Haar, and
   `paperArithmeticHaar_hull_mass_of_sourceQ` gives the C6 hull-mass form.  So
   the whole residual content is one named arithmetic hypothesis.

9. [PROVED, quoted input] **S865 norm-power law in log form**
   (`rootHaarFactor_log_norm_pow`, from
   `S865RootHaarFactorNormPowActual.rootHaarFactor_normPow_actual` via the S861
   character/norm comparison):
   `Real.log (distribHaarChar (rootNormedExtension T b) lam) = d * Real.log ||lam||`.
   The C6 hull norm-power theorem (item 4) has exactly this shape.  The two
   carriers are *not* identified in the tree (`rootNormedExtension T b` for the
   paper Theta values vs the completion tensor `ArithmeticTupleTupleBlock`), and
   that unproved carrier identification (S342 gap) is the substance of the first
   missing — not a normalization question.

## Exact first missing (statement)

    S1931FirstMissing places tuple C3
      := arithmeticTupleHullUnitLogVolume places tuple
           = (c3ThetaSignedProcession C3).average

equivalently

    Real.log C3.thetaPacket.q
      = - (arithmeticTupleHullUnitLogVolume places tuple * (c3ThetaCard : Real))
          / sourceThetaWeightSum l,

equivalently (C6 canonical hull mass at the source Haar)

    paperArithmeticHaar places tuple mu (arithmeticTupleCanonicalHull places tuple)
      = ENNReal.ofReal (Real.exp ((c3ThetaSignedProcession C3).average)).

The target identity at the source Haar holds **iff** this holds
(`s1931_firstMissing_iff_comparison`); by item 7 it is false for every packet
with `q > 1`, so it cannot be proved from the source normalization alone.

## Lean artifacts

Target file:
  `tmp/sheaf/xif/paper/S1931SourceHaarSignedAverageActual.lean`
  (compile exit recorded below)

Text (UTF-8, pre-compile, contains no sorry/admit/axiom/True/PUnit):
  bytes 36359
  SHA256 52EA9675606F080D4F3B165A001E0E564FD64F3808EEF6E66BC33F5AD977E8E5

Compile (from D:\lean):
  `lake env lean -R D:/lean -s 65536 -M 8192      -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1931SourceHaarSignedAverageActual.olean      tmp/sheaf/xif/paper/S1931SourceHaarSignedAverageActual.lean`
  EXIT=0, zero errors, zero warnings.
  `#print axioms` for the 20 probed declarations: only
  `[propext, Classical.choice, Quot.sound]`.
  Compile log: `tmp/sheaf/xif/paper/_S1931_compile.log` (3194 bytes).

Olean:
  `.lake/build/lib/lean/tmp/sheaf/xif/paper/S1931SourceHaarSignedAverageActual.olean`
  bytes 589568
  SHA256 D8D79204A4E178EBD3993DA4A493546BC4CBF8B38756F9D581F07A448783D163

Consumer probe:
  `tmp/sheaf/xif/paper/_S1931ConsumerProbe.lean` EXIT=0, 0 errors/warnings
  (imports the olean, uses `s1931_firstMissing_iff_comparison`,
  `signedUnitFactor_of_sourceQ`, `paperArithmeticHaar_unitReference`,
  and prints the full bundled content signature).
  Log: `tmp/sheaf/xif/paper/_S1931_consumer.log`.

Upstream files: not modified (S1916, HaarSignedAverageProof, S865, S1904
unchanged).

## Boundary

- `target_accepted = false`: `SignedUnitFactorThetaComparison` at the source Haar
  is not proved; it is reduced to the named `S1931FirstMissing` and shown to be a
  genuine constraint on the source theta packet (false for `q > 1`).
- No arbitrary `mu` remains in the missing: the comparison is proved independent
  of the initial additive Haar (`sourceHaar_comparison_independent_of_initialHaar`).
- No fake normalization: the source Haar is the actual unit-region normalization
  of an actual additive Haar measure; the hull mass is then *computed*, not
  chosen.
- The S865 norm-power law is quoted in log form; transporting it to the C6
  carrier is the missing identification (S342 carrier gap), not something this
  file assumes.
- Not run: full project build (`lake build LeanFormal`), comparator acceptance,
  central watchdog queue, independent human review.  This is a delegated
  subagent package; `coord/queue.md`, `coord/STATE.md`,
  `AUDIT_LEDGER.md` are left to the coordinator.
