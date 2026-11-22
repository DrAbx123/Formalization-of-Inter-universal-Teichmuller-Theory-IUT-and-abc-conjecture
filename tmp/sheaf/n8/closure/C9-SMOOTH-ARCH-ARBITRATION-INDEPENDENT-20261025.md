# C9 smooth arch factor arbitration (independent)

Task: task-400 (Independent arch factor arbitration). Owner: volumedet.
Date: 2026-10-25. Short arbitration only. No black box, no arbitrary data,
no mixed/E3, no Lean/Project edits. Only this file written.
`target_accepted=false`.

Inputs: C6 Lean definitions `C6ActualIQData.lean`, `C6ActualIdentification.lean`,
`C6NormalizationProof.lean`; C9 global assembly/arch B_I-zero notes; IUT III
Cor3.12/Prop3.9 packet+procession normalization; C9-P6NORM-FACTOR and
C9-SMOOTH-TARGET audits.

## 0. Arbitration verdict

The exact global formula is

    h_C = h_bad_can/d + h_inf,   d=41,                         (0.1)

NOT `h_C=h_can/d` globally. The Lean C6 `normalizedLogVolume` is defined on
the finite `ArithmeticTensorTupleBlock` and carries the finite-block factor
`1/finrank=D=41`; it has no archimedean component. The C9 global h_C adds the
archimedean B_I-zero `h_inf` separately, undivided by D. The source Θ-pilot
log-volume h_can is the global packet+procession log-volume (finite bad plus
arch). Therefore

    h_can = h_bad_can + h_inf,
    h_C = h_bad_can/d + h_inf,
    h_can = d*h_C - (d-1)*h_inf.                              (0.2)

The two candidate formulas agree only when d=1 or h_inf=0; otherwise they
differ by `(1-1/d)h_inf`. Formula (0.1) is correct; `h_C=h_can/d` is not.

## 1. Lean C6 evidence

`C6ActualIQData` is explicitly defined on the finite carrier

    C6IQCarrier := ArithmeticTensorTupleBlock places tuple

with

    normalizedLogVolume := arithmeticTupleNormalizedLogVolume places tuple mu,
    normalizationWeight := 1 / (finrank_Qp (ArithmeticTensorTupleBlock ...)).

`C6ActualIQData.actual` and `IsActual` identify these fields by `rfl`.
`C6NormalizationProof.normalizedLogVolume_eq_normalization_mul_log_ratio`
proves

    normalizedLogVolume S = normalizationWeight * (log μ(S) - unitReferenceLog),

with normalizationWeight=1/D. There is no archimedean place or arch term in
the C6 carrier/definition. This is exact Lean-level evidence, not a C9
convention choice.

Thus `h_bad,norm = h_bad,can/d` for the finite bad block: the same signed
finite log divided by D=d.

## 2. C9 global h_C and arch

The C9 global volume is assembled as

    h_C = sum_{p in S_bad} alpha_p h_p + sum_good + h_inf(C),   (2.1)

where the finite bad h_p use C6 normalizedLogVolume (factor 1/D=d) and h_inf
is the separate B_I-zero archimedean readout

    h_inf = log r_inf  (F_mod=Q, one real place; alpha_inf=1).   (2.2)

`h_inf` is not an `ArithmeticTensorTupleBlock` normalized volume and does not
carry the finite D=41 division. Therefore the global h_C is a **mixed sum**:
finite block canonical/d plus arch undivided. This proves (0.1) under the
standard C9 interpretation.

## 3. Source normalization

IUT III Prop3.9(i) packet-normalization (multiplication by e adds1) and
procession normalization (average over j∈F_l^×) are used in Cor3.12 for
`-|logΘ|` and `-|logq|`. They are not the C6 finite-block 1/D normalization.
Source global log-volume is the sum of local packet log-volumes over places;
there is no finite-block D division of the arch local term. Under the
B_I-zero arch alignment, the source arch packet log equals h_inf (for F=Q
alpha_inf=1). Hence

    h_can = h_bad_can + h_inf,                                (3.1)

as in (0.2). If one instead divided the entire h_can by d, one would be
imposing a uniform global 1/d normalization that neither C6's finite-only
normalizedLogVolume nor Prop3.9 packet normalization supplies.

## 4. Correct P6 relation

Cor3.12 gives

    Q_can <= h_can = d*h_C - (d-1)*h_inf.                    (4.1)

Hence the exact translated target is

    Q_can/d + ((d-1)/d)*h_inf <= h_C.                        (4.2)

Consequences:

- P6_can: `Q_can<=h_can` exact source statement.
- P6_norm: `Q_can/d<=h_C` follows from (4.1) iff `h_inf>=0`; if h_inf<0,
  (4.1) is weaker and does not imply P6_norm.
- Mixed target `Q_can<=h_C`: off by d and arch.
- If one incorrectly uses `h_C=h_can/d`, one obtains the stronger/simpler
  P6_norm without arch correction; that is the false branch of the
  arbitration.

## 5. Arch normalization itself

B_I-zero: logvolume(B_I)=0, radial h_v=log r_v; global alpha_v=d_v/[F:Q].
For F=Q, one real place, alpha_inf=1, h_inf=log r_inf. This is the IV
archimedean normalization; it is not a finite tensor-block normalization.
The source arch packet log under B_I-zero is the same radial log (no finite
D factor). Any conversion of h_inf to canonical/degree normalization would
require multiplying by a separate archimedean degree/factor; no such factor
is present in the C6/C9 definitions. Therefore arch remains undivided in
h_C.

If one adopted a different global normalization where all places are divided
by d, then h_C=h_can/d and task-383 formula would hold. But that is not the
current C6 finite-block + C9 arch assembly; it is a different target
convention. The arbitration rejects it for the actual C9 target.

## 6. Exact statement

Theorem (arch arbitration). Under the C6 finite-block definition and the C9
B_I-zero global assembly, the exact relation between the source packet
log-volumes and C9 h_C is (0.2). Consequently:

(i) P6_can `Q_can<=h_can` holds by Cor3.12;
(ii) P6_norm `Q_can/d<=h_C` follows from Cor3.12 plus `h_inf>=0`;
(iii) the exact unconditional translated target is
      `Q_can/d+((d-1)/d)h_inf<=h_C`;
(iv) the mixed `Q_can<=h_C` and the global `h_C=h_can/d` are both false
      in general.

Proof. C6 normalizedLogVolume equals finite canonical/d; h_C adds h_inf
separately; source h_can includes h_inf; algebra as in (0.2). The remaining
sign condition is h_inf>=0. QED.

## 7. Classification

PROVED/LEAN-SOURCE:

- C6 normalizedLogVolume finite ArithmeticTensorTupleBlock, factor 1/D.
- C6 normalizationWeight=1/finrank finite block, D=d=41.
- C9 h_C = finite normalized sum + separate arch h_inf.
- Exact h_can=d h_C-(d-1)h_inf; h_C=h_can/d iff d=1 or h_inf=0.
- Correct P6_norm condition h_inf>=0 / exact target with h_inf.

CONDITIONAL:

- B_I-zero arch equals source packet arch (no extra factor);
- C6 provenance/target identification; q-pilot 82-root (Qcan=-b/e, no extra
  82); actual h_inf.

WITHDRAWN:

- `h_C=h_can/d` globally;
- P6_norm without arch correction/without h_inf>=0;
- mixed `Q_can<=h_C`.

## 8. Conclusion

Arbitration: formula (0.1) `h_C=h_bad_can/d+h_inf` is correct; the global
`h_C=h_can/d` is false. The exact translated P6 target is
`Q_can/d+((d-1)/d)h_inf<=h_C`; P6_norm follows only with `h_inf>=0`, and
P6_can is exactly Cor3.12. The arch component is not divided by the finite
block degree d=41. No black box, no arbitrary data, no mixed/E3, no Lean
edits.

## 9. Status

Arbitration only. Only this file written. `target_accepted=false`; P6_can
source; P6_norm conditional on h_inf>=0; exact arch-corrected target
available.
