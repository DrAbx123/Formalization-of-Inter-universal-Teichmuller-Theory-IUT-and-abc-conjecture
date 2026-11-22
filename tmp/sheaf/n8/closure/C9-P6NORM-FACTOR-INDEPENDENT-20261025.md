# C9 P6 normalization/factor audit: P6_norm vs P6_canon

Task: task-383 (Independent exact P6 normalization/factor audit). Owner:
volumedet. Date: 2026-10-25. Short exact theorem/audit only. No black box,
no arbitrary data, no mixed/E3, no Lean/Project edits. Only this file
written. `target_accepted=false`.

Inputs: IUT III Cor3.12/Prop3.9 packet- and procession-normalization;
C9-COR312-QPILOT-20261025.md; C9-CANONICAL-NORM-ATTACK (E15); C9-P6
normalization decision; C9-THETA-ROOT-CANONICAL; C6
`normalizedLogVolume` definitions.

## 0. Exact result

Let

    Q_can := -|log q|_packet   (source q-pilot, canonical packet log),
    h_can := -|log Θ|_packet   (source Θ-pilot, canonical packet log),
    Q_norm := Q_can / d,   h_norm := h_can / d,   d=[F_v:Q_p]=41. (0.1)

Cor3.12 proves, in the source packet normalization,

    Q_can <= h_can.                                             (0.2)

After C6: `h_C=h_norm` (C6 normalizedLogVolume has the 1/D factor);
`Q_canon` is the canonical QPaper q log.

Then:

    P6_norm:  Q_C^norm <= h_C,   i.e. Q_can/d <= h_norm,       (0.3)
    P6_can:   Q_C^can <= h_C^can = d*h_norm,                   (0.4)

are both equivalent to (0.2) and are **true** (conditional on Cor3.12 A1-A3
and the C6/source identifications). But the **mixed** target

    Q_C^can <= h_C^norm                                          (0.5)

is not (0.2); it is off by the exact factor d=41: (0.2) gives
`Q_C^can <= d*h_C`, not `Q_C^can<=h_C`.

The q-pilot 82-root normalization is already absorbed in `Q_can=-b/e logp`
(qhat=pi^b canonical log); replacing qhat by the full q=qhat^{2l} would
multiply Q by 2l=82, and is NOT the source q-pilot normalization. Thus the
only factor in P6_canon vs P6_norm is d=41, not 82 or 82d.

## 1. Source normalization is packet, not C6 degree

IUT III Prop3.9(i): the log-volumes are normalized so that multiplication by
e=2.718... corresponds to adding 1; this is the **packet-normalization**.
Prop3.9(i) also defines the **procession-normalization** as the average over
the capsules/labels j∈F_l^×. Cor3.12 uses this packet+procession log-volume
for both `-|logΘ|` and `-|logq|`. It does not contain the C6 `1/D`
arithmetic-tensor degree division.

C6's `normalizedLogVolume` is `arithmeticTupleNormalizedLogVolume`,

    (1/D) ( log μ(S) - log μ(unit reference) ),

i.e. a degree-normalized arithmetic tensor volume with D=finrank_{Q_p}
block. In the C9 tame type D=d=41. Therefore

    h_C = h_can / d,     (C6 normalized).                      (1.1)

This corrects the task-381 H3 assumption `h_C=-|logΘ|` without a factor:
the source packet log and the C6 normalized log differ by d. With the
correction, `h_can=d h_C` and Cor3.12 (0.2) gives (0.4)/(0.3), not (0.5).

## 2. q-pilot 82-root normalization

C9/local model:

    qhat=pi^b,  q = qhat^{2l},  2l=82,  b=3 or273;
    canonical packet log of qhat = -b/e log p.                   (2.1)

Theta values are `qhat^{j²}` (equivalently `a^{j²}` with a^{2l}=q); the
physical Gaussian value profile is root-rotation invariant (task-294/296).
The q-pilot object is built from this qhat normalization, so

    Q_can = -b/e logp = -|log q|_packet,                        (2.2)

which is exactly the C9 Q value (e.g. b=3: -3/41 logp). If one instead used
the full q=qhat^{2l} canonical log, one would get

    -|log q_full|_packet = 2l * (-b/e logp) = 82 Q_can,         (2.3)

an extra factor 82. That is not the source q-pilot object: the source theta
values are qhat^{j²}, and the q-pilot uses the same 2l-root normalization.
Root rotation a->ζa is absorbed by the source root units and does not create
a new factor.

Thus Q_can is the correct source q-pilot value; no 82 factor enters
P6_norm/P6_canon. The factor is the completion degree d=41.

## 3. Exact factor relation

E15 (C9-CANONICAL-NORM-ATTACK) proves for nonzero q:

    Q_can = d * Q_norm,   Q_norm = Q_can/d,   d=[F_v:Q_p],
    equality only d=1.                                          (3.1)

In the C9 tame totally ramified type d=e=ell=41. The C6 normalized theta
volume is similarly `h_norm=h_can/d`. Therefore:

    Q_can = d Q_norm,   h_can = d h_norm,   d=41.               (3.2)

Cor3.12 `Q_can<=h_can` is equivalent to `Q_norm<=h_norm`. The mixed
canonical-Q/normalized-h target is

    Q_can <= d h_C = h_can,  i.e. Q_can/d <= h_C.               (3.3)

Only after dividing Q_can by d (or multiplying h_C by d) does one recover
P6. This is exact and not a missing theorem.

## 4. P6_norm vs P6_canon

Theorem 4.1 (normalized P6). Assume Cor3.12 A1-A3 and the C6/source
identifications above (C6 h_C=h_norm; Q_C=Q_norm). Then

    Q_C <= h_C,   i.e. Q_norm<=h_norm.                          (4.1)

Proof. Cor3.12 gives Q_can<=h_can; divide by d using (3.2). QED.

Theorem 4.2 (canonical P6). If both sides are taken canonically,

    Q_C^can <= h_C^can = d h_C.                                 (4.2)

This is equivalent to (4.1) and true. But it is NOT `Q_C^can<=h_C`.

Theorem 4.3 (mixed target obstruction). The mixed statement

    Q_C^can <= h_C (normalized)                                  (4.3)

does not follow from Cor3.12; it would require
`Q_can<=h_can/d`, which is false in general by the exact factor d=41. The
only inequality available is `Q_can<=d h_C`.

Thus: **P6_norm is exact; P6_canon requires the canonical h (or Q/d); the
mixed canonical-Q/normalized-h target is off by d.**

## 5. Procession and B_I-zero

- Procession: source average over j∈F_l^× (packet+procession normalization).
  C9 row average is 1/m, m=(l-1)/2=20, with ±j pairing. The paired source
  labels give the same qhat^{j²} profile, so the two averages agree; no extra
  1/2 factor. (If a different label/weight convention is used, this must be
  rechecked; it is not a d factor.)
- B_I-zero: the C9 arch convention is `logvolume(B_I)=0`, `h_inf=log r`.
  It is a normalization of the arch reference; it does not change the finite
  canonical/normalized d factor. H3 from task-381 must be replaced by the
  explicit `h_can=d h_C` relation, not by `h_C=h_can`.

## 6. Exact gaps / conditions

(C1) Cor3.12 A1-A3 source schema (task-377); no explicit C needed.
(C2) C6 provenance map identifies h_C with the source Θ-pilot normalized
hull volume; otherwise h_C remains a C6 normalized volume, not automatically
`h_can/d`.
(C3) C6 normalizedLogVolume has exactly the 1/D factor with D=d=41;
if a different block normalization is used, adjust the factor accordingly.
(C4) Q convention: normalized PaperP6 qLog vs canonical QPaper; the target
must choose one. This is the E15 exact factor.
(C5) Procession ±j pairing and B_I-zero arch alignment.

These are explicit source-alignment conditions, not black-box steps.

## 7. Classification

PROVED/EXACT:

- Source Cor3.12 uses packet+procession log-volumes; `Q_can<=h_can`.
- q-pilot 82-root: Q_can=-b/e logp; full q would add factor 2l=82 (wrong).
- Q_can=d Q_norm, h_can=d h_norm, d=41.
- P6_norm: Q_norm<=h_norm exact from Cor3.12.
- Mixed Q_can<=h_norm false in general; correct is Q_can<=d h_norm.

CONDITIONAL:

- C6 provenance/identification; procession ±j; B_I-zero; target Q
  convention.

WITHDRAWN/CORRECTED:

- task-381 H3 `h_C=-|logΘ|` without d; corrected to h_C=h_can/d.
- adding an extra 82 factor to Q_can (full q confusion).
- original mixed P6 `Q_can<=h_C` as a Cor3.12 consequence.

OPEN:

- C6 provenance alignment / actual source target identification; P6 in the
  chosen normalized convention once C2-C5 are established.

## 8. Conclusion

The exact decision is: P6_norm (`Q_norm<=h_norm`) follows from Cor3.12
A1-A3; P6_canon must be written `Q_can<=h_can=d h_C`; the mixed target
`Q_can<=h_C` is off by the exact factor d=[F_v:Q_p]=41. The q-pilot 82-root
normalization is already in Q_can=-b/e logp and does not add 82. C6's
normalizedLogVolume supplies h_C=h_can/d. No black box, no arbitrary data,
no mixed/E3, no Lean edits.

## 9. Status

Normalization/factor audit only. Only this file written. `target_accepted=false`;
P6_norm exact conditional on C1-C5; P6_canon corrected by d; original mixed
P6 off by 41.
