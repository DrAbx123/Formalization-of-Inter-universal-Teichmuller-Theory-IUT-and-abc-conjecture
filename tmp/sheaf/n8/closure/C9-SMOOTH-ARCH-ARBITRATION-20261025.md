# C9 smooth arch factor arbitration: h_C = h_bad/d + h_inf vs h_can/d

Task: task-399. Owner: qside. Date: 2026-10-25.
Arbitration and exact formula; no black box; no mixed/E3; no Lean edits;
only this file written.

## 0. Verdict

The correct global arch relation is

    h_C = h_bad_can/d + h_inf,        d = 41,                 (0.1)

NOT h_C = h_can/d globally.  The Lean C6 normalizedLogVolume is defined only
on the finite ArithmeticTensorTupleBlock and carries the finite-block factor
1/finrank = 1/d.  The archimedean B_I-zero readout h_inf is added separately
by the C9 global assembly and is not divided by d.

Source packet quantity:

    h_can = h_bad_can + h_arch_can,
    h_arch_can = h_inf   (B_I-zero arch alignment).           (0.2)

Therefore

    h_can = d*h_C - (d-1)*h_inf,                              (0.3)
    h_C = h_can/d  iff  d=1 or h_inf=0.                       (0.4)

The exact translated P6 target is

    Q_can/d + ((d-1)/d)*h_inf <= h_C.                         (0.5)

Consequences:

- P6_can  (Q_can<=h_can) is exactly Cor3.12 and is conditionally true.
- P6_norm (Q_can/d<=h_C) follows from Cor3.12 plus h_inf>=0; without
  h_inf>=0 it does NOT follow.
- Mixed target Q_can<=h_C is not valid; it is off by d and arch.
- The alternate global h_C=h_can/d is not the actual C6/C9 assembly; it would
  require dividing the arch component by d as well.

## 1. Lean evidence for the finite-only C6 factor

### 1.1 arithmeticTupleNormalizedLogVolume

LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceNormalizedUnitScalingLogVolume.lean
lines 89-98:

    def arithmeticTupleNormalizedLogVolume
        [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
        (μ : Measure (ArithmeticTensorTupleBlock places tuple))
        (S : Set (ArithmeticTensorTupleBlock places tuple)) : ℝ :=
      (1 / (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : ℝ)) *
        (Real.log (μ S).toReal - Real.log
          (μ (arithmeticTupleCanonicalUnitReference places tuple)).toReal)

The entire definition is on the finite tensor block.  There is no
archimedean carrier, no infinite-place factor, and no arch term.  The
normalization is exactly 1/D, D = finrank_Qp(ArithmeticTensorTupleBlock).

### 1.2 C6ActualIQData

tmp/sheaf/n8/closure/C6ActualIQData.lean lines 30-43:

    abbrev C6IQCarrier := ArithmeticTensorTupleBlock places tuple
    structure C6ActualIQData where
      hull ...
      iqInterface ...
      signedHullLog ...
      normalizedLogVolume : Set C6IQCarrier → ℝ :=
        arithmeticTupleNormalizedLogVolume places tuple mu
      unitReferenceLog ...
      normalizationWeight : ℝ :=
        1 / (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock ...) : ℝ)

Again the carrier and normalizationWeight are finite-block only.  The
structure has no archimedean coordinate.

### 1.3 Identification

C6ActualIdentification.lean lines 31-44: the IsActual fields identify the
normalizedLogVolume with arithmeticTupleNormalizedLogVolume and
normalizationWeight with 1/finrank.  C6NormalizationProof.lean lines 71-87
proves

    B.normalizedLogVolume S
      = B.normalizationWeight * (log μ(S) - B.unitReferenceLog),

with normalizationWeight=1/D.  There is no arch division in this theorem.

Thus for the finite bad block:

    h_bad_C6 = h_bad_can / D = h_bad_can / d.                 (1.1)

## 2. Why h_inf is not divided

C9 global h_C is assembled from:

    h_C = sum_{p in S_bad} alpha_p h_p + sum_good + h_inf(C),   (2.1)

where:
- finite bad h_p use the C6 normalizedLogVolume (factor 1/d);
- good finite places have zero normalized contribution in the C9
  normalization;
- h_inf is the separate B_I-zero archimedean readout
      h_inf = sum_{v|infty} alpha_v [h_v^ang + log r_v],
  with logvolume(B_I)=0 and radial h=log r.

The arch term is not an ArithmeticTensorTupleBlock volume; it has no
finite-block finrank and cannot inherit the 1/d factor.  Hence the global
h_C is a mixed sum:

    h_C = h_bad_can/d + h_inf.                                (2.2)

This is the exact C9 assembly, not a convention choice.

## 3. Source side and alignment

IUT III Proposition 3.9(i) packet-normalization:
- arch complex O has log-volume 0; multiplication by e adds 1;
- nonarch O has log-volume 0; multiplication by p_v adds -log p_v;
- procession-normalization averages over the capsules/j labels.

Cor3.12's h_can=-|log Theta| is the global packet+procession log-volume:
finite bad packet log plus arch packet log:

    h_can = h_bad_can + h_arch_can.                           (3.1)

The B_I-zero arch alignment identifies the source arch packet log with the
C9 arch readout:

    h_arch_can = h_inf                                       (3.2)

(for F=Q, one real archimedean place, alpha_inf=1; in general the same
alpha_v/d_v weights are used on both sides).

Then:

    h_can = h_bad_can + h_inf
          = d*(h_bad_can/d + h_inf) - (d-1)*h_inf
          = d*h_C - (d-1)*h_inf.                              (3.3)

If instead one writes h_C=h_can/d globally, then

    h_can/d = h_bad_can/d + h_inf/d,

which divides the arch term by d.  This is not the source packet
normalization and not the C9 B_I-zero arch assembly; it is a different global
normalization.

## 4. Exact P6 translation

Cor3.12 gives

    Q_can <= h_can = d*h_C - (d-1)*h_inf.                     (4.1)

Divide by d>0:

    Q_can/d <= h_C - ((d-1)/d)*h_inf,
    Q_can/d + ((d-1)/d)*h_inf <= h_C.                         (4.2)

This is the exact arch-corrected target.

Define Q_norm=Q_can/d.  P6_norm is Q_norm<=h_C.  From (4.2):

- if h_inf>=0, then h_C-((d-1)/d)h_inf <= h_C, so P6_norm follows;
- if h_inf<0, the exact bound is weaker than P6_norm; no conclusion.

P6_can is Q_can<=h_can, exactly (4.1)/(3.3), and is the source statement.

Mixed target Q_can<=h_C would require

    Q_can <= h_C = h_bad_can/d + h_inf,

which is not (4.1); it is off by d on the finite block and by arch.
For example with d=2, h_C=0, h_inf=-1, h_can=1, Q_can=1:
Q_can<=h_can but Q_can=1>h_C=0; Q_can/d=1/2>0.  This shows both the mixed
target and P6_norm without h_inf>=0 fail.  (The actual d is 41; the
counterexample is only an algebraic sign check.)

## 5. Exact arch normalization formula

The arch component is normalized by B_I-zero:

    logvolume(B_I) = 0,
    h_v^rad(B_v(r_v)) = log r_v,
    h_inf = sum_{v|infty} alpha_v [h_v^ang + log r_v].

It is not divided by d.  The finite bad component is C6-normalized:

    h_bad_norm = (1/D) [log μ(hull) - log μ(unit)] = h_bad_can/d.

The two components live in different normalizations; the global h_C is their
sum (2.2).  This is the arbitration: the arch factor is 1, not 1/d.

If one insists on a uniform global 1/d normalization, one must redefine h_C
to include h_inf/d; that is a different target convention, not the C6/C9
actual convention.  The source Cor3.12 inequality then changes accordingly
(and h_C=h_can/d would hold only in that redefined convention).

## 6. Target convention decision

The following are three distinct statements and must not be mixed:

(P6_can)   Q_can <= h_can.                    source Cor3.12; conditional A1-A3.
(P6_norm)  Q_norm=Q_can/d <= h_C.             requires h_inf>=0 (or exact arch
                                              correction); not unconditional.
(P6_arch)  Q_can/d + ((d-1)/d)h_inf <= h_C.   exact translated target from
                                              Cor3.12; always valid under
                                              A1-A3 + (0.1).

Mixed Q_can<=h_C is none of these and is false in general.

The exact source target is P6_can; the exact C9 global target is P6_arch;
P6_norm is the simplified target only under h_inf>=0.

## 7. Exact gaps

(A1) C6 finite-block definition and provenance: normalizedLogVolume is
     arithmeticTupleNormalizedLogVolume on ArithmeticTensorTupleBlock,
     normalizationWeight=1/finrank.  This is Lean-source evidence, not a
     missing theorem.
(A2) Arch alignment h_arch_can=h_inf under B_I-zero and the same alpha_v
     weights.  If arch is normalized differently, (0.1) changes by an
     explicit additive/scaling term.
(A3) Cor3.12 A1-A3 source schema and Q_can<=h_can (conditional).
(A4) h_inf>=0 is NOT proved; B_I-zero is only a normalization, and the IV
     container gives only an upper bound.  Therefore P6_norm is not
     unconditional; use P6_arch or add an arch lower bound.
(A5) q-pilot 82-root normalization is already inside Q_can=-b/e; it does not
     add a factor 82 to d.

No arbitrary arch value, no mixed/E3 profile, no explicit C is inserted.

## 8. Classification

PROVED/LEAN-SOURCE:
- arithmeticTupleNormalizedLogVolume = (1/finrank)*log-ratio on the finite
  ArithmeticTensorTupleBlock; no arch component.
- C6ActualIQData normalizationWeight = 1/finrank.
- finite bad block: h_bad_norm = h_bad_can/d.
- C9 h_C = finite normalized sum + separate arch h_inf.
- exact h_can=d*h_C-(d-1)h_inf; h_C=h_can/d iff d=1 or h_inf=0.
- exact P6_arch target (0.5).

CONDITIONAL:
- B_I-zero arch packet alignment h_inf=h_arch_can;
- Cor3.12 A1-A3 and Q_can<=h_can;
- C6 target identification.

WITHDRAWN:
- global h_C=h_can/d;
- P6_norm without h_inf>=0 or exact arch correction;
- mixed Q_can<=h_C;
- dividing the arch h_inf by the finite-block d=41.

## 9. Conclusion

Arbitration: the exact formula is

    h_C = h_bad_can/d + h_inf,

not h_can/d.  The Lean C6 normalizedLogVolume is finite-block only
(1/finrank=d=41); the C9 arch B_I-zero h_inf is separate and undivided.
Consequently

    h_can = d*h_C - (d-1)*h_inf,
    Q_can <= d*h_C - (d-1)*h_inf,
    Q_can/d + ((d-1)/d)*h_inf <= h_C.

P6_can is source; P6_arch is the exact translated target; P6_norm follows
only with h_inf>=0.  The alternate h_C=h_can/d is the false uniform-global-
division branch.  No black box, no arbitrary data, no mixed/E3, no Lean
edits.

target_accepted=false.

## 10. Sources

- LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceNormalizedUnitScalingLogVolume.lean
  lines 89-98: arithmeticTupleNormalizedLogVolume, finite block 1/finrank.
- tmp/sheaf/n8/closure/C6ActualIQData.lean lines 30-43: C6IQCarrier,
  normalizedLogVolume, normalizationWeight=1/finrank.
- tmp/sheaf/n8/closure/C6NormalizationProof.lean lines 71-87:
  normalizedLogVolume_eq_normalization_mul_log_ratio.
- tmp/sheaf/n8/closure/C6ActualIdentification.lean lines 31-44:
  IsActual identifications.
- C9-P6-SMOOTHNESS-AUDIT-20261025.md B6/B7: conflict task-395 vs task-397.
- C9-SMOOTH-TARGET-INDEPENDENT-20261025.md: exact h_C=h_bad/d+h_inf.
- C9-P6NORM-FACTOR-INDEPENDENT-20261025.md: factor d=41; Qcan=-b/e; no 82.
- IUT III Proposition 3.9(i), Corollary 3.12: packet/procession and
  Q_can<=h_can; IUT-III.txt SHA256
  822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D.
