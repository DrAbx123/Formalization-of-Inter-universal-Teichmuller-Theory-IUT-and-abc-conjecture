# C9 independent target translation and factor audit

Task: task-381 (Independent target translation and factor audit). Owner:
volumedet. Date: 2026-10-25. Natural-language audit/theorem schema only. No
black-box, no arbitrary data, no mixed/E3, no Lean/Project edits. Only this
file written. `target_accepted=false`.

Inputs: IUT III Cor3.12 statement/proof (`sources/IUT-III.txt`) and
C9-COR312-QPILOT-20261025.md; C9-CANONICAL-NORM-ATTACK-20261025.md (E15);
C9-AUDIT-MASTER-ROUTE-20261025.md (§3 E15); C6 normalization
(`C6NormalizationProof`, `C6ActualIdentification`); C9-PAPER-TARGET-STAGE2;
C9-UNIFORM-SAT-U §1.5; C9-ARCH-NORMALIZATION-CORRECTION (B_I-zero).

## 0. Result

Cor3.12 uses **procession-normalized mono-analytic log-volumes**:

    -|log Θ|  (normalized),     -|log q|  (normalized).          (0.1)

C9 h_C is a C6 **normalized** log-volume (1/D factor in
`arithmeticTupleNormalizedLogVolume`), and after the C6/procession/B_I-zero
alignment it matches the source normalized `-|log Θ|`, with no canonical
factor d on the h side (conditional on the C6 alignment map).

C9 Q_C has a normalization ambiguity:

- **Normalized Q** (PaperP6 qLog / source convention): `Q_C = -|log q|`
  exactly; then P6 `Q_C<=h_C` follows from Cor3.12 A1-A3 with
  `h_C=-|log Θ|`, without an explicit C.
- **Canonical Q** (C9Paper `QPaper.qPilotLogVolume = localSignedLog`):
  `Q_C = d * (-|log q|)`, where `d=[F_v:Q_p]` (C9 tame totally ramified
  d=e=41). Then Cor3.12 gives `Q_C/d <= h_C`, i.e.
  `Q_C <= d*h_C`, **not** the canonical P6 `Q_C<=h_C`.

Thus the translation is exact only in the normalized convention. If the
target uses canonical QPaper Q, the comparison has exact factor d=41 and
must be stated as `Q_canon/d <= h_C` or `Q_canon <= d*h_C`; it is not the
paper P6 inequality without that conversion. The factor is not an unknown
error: E15 proves it.

## 1. Source normalization in Cor3.12

Cor3.12 defines

    -|log Θ| = procession-normalized mono-analytic log-volume of the
    holomorphic hull of the union of possible images of the Θ-pilot,
    relative to Kummer isomorphisms, subject to Ind1/Ind2/Ind3;

    -|log q| = procession-normalized mono-analytic log-volume of the
    image of the q-pilot, not subject to Ind1/Ind2/Ind3.         (1.1)

The word 'procession-normalized' means the average over `j in F_l^×` with
the III Rmk3.1.1(ii)-(iv)/Prop3.9 normalized weights; it is not the raw
pointwise maximum over j and not an unnormalized Haar integral over a single
capsule. The q-pilot value is a normalized real number (negative log-volume);
|log q|>0.

This is the source convention. Any C9 quantity identified with (1.1) must use
the same normalized readout, not the canonical localSignedLog without the
degree division.

## 2. C6 h_C alignment

C6's `normalizedLogVolume` is `arithmeticTupleNormalizedLogVolume`, which
divides the log Haar volume by the Q_p-finrank `D` of the arithmetic tensor
block (`1/D` factor); it is the normalized, not the canonical, local readout.
In the C9 tame type, `D=d=41`, and C6's normalization is the C6 analogue of
the source local degree normalization.

With the C6 actual identification

    B.normalizedLogVolume = arithmeticTupleNormalizedLogVolume places tuple μ

and the C9 global assembly using the same degree weights/procession average
and B_I-zero arch convention, h_C is the C6 normalized hull volume. Therefore
the intended translation is

    h_C = -|log Θ|   (normalized source volume),                (2.1)

**conditional on**:

(H1) the C6 provenance map from the source Θ-pilot possible-image set to the
C6 tensor block/hull is the actual map (not an arbitrary set);
(H2) the procession average over j in F_l^× equals the C9 row average;
(H3) the archimedean B_I-zero normalization is the one used in the source
global log-volume/Prop3.9 readout.

These are conditional source-identification inputs, not new assumptions;
without them h_C is a C6 normalized volume, not automatically the source
`-|log Θ|`.

### 2.1 Procession factor

Source averages over `j in F_l^×` (l-1=40 labels). C9's row average is
`1/m sum_{j=1}^m`, m=(l-1)/2=20. The label pair ±j has the same theta value
(q^{j^2} with j and l-j giving the same exponent), and the source normalized
weights are uniform on the paired labels. Hence the paired average equals
the m-average: no extra 1/2 factor. This is exact for the standard theta
label symmetry; if one uses a different labeling/weight, the factor must be
recomputed.

### 2.2 B_I-zero arch

The binding C9 arch convention is B_I-zero: logvolume(B_I)=0, h_inf=log r
(after the correction of task-171/172). Cor3.12's global normalized
log-volume uses the source (IV) normalization; C9's B_I-zero is the audited
IV convention. Under H3 the arch components agree. If one instead uses the
withdrawn shell-pi convention, the comparison changes (shell-pi h_inf=log(r/π),
different zero reference); that convention is not used.

## 3. C9 Q_C: exact relation or factor d

Two distinct C9/paper Q objects occur:

    Q_canon = localSignedLog(qCandidate)          (C9Paper QPaper)
    Q_norm  = Real.log ||qUnit||_normalized      (PaperP6 qLog)

E15 (C9-CANONICAL-NORM-ATTACK, task-174) proves the exact relation

    Q_canon = d * Q_norm,    d=[F_v:Q_p],
    Q_norm = Q_canon / d,                                  (3.1)

and equality only when d=1. In the C9 tame totally ramified type
`d=e=ell=41`, so Q_canon=41*Q_norm.

Cor3.12's q-pilot value is normalized:

    -|log q| = Q_norm.                                      (3.2)

Therefore:

(Q-exact) if C9 uses Q_norm, `Q_C=-|log q|` exactly;
(Q-factor) if C9 uses Q_canon, `Q_C=d*(-|log q|)` exactly, i.e.
`-|log q|=Q_C/d`.

The source Cor3.12 inequality `-|log q| <= -|log Θ|` then becomes:

    Q_norm <= h_C            (normalized P6),
    Q_canon/d <= h_C         (the same, written in canonical Q),
    equivalently Q_canon <= d*h_C, not Q_canon<=h_C.       (3.3)

Thus if the target P6 is read on the canonical QPaper side while h_C is the
C6 normalized Θ side, the comparison is off by d=41 on the Q side. This is
the E15 mismatch; it is not a missing theorem and not a small error.

## 4. Target translation theorem

Theorem 4.1 (normalized target translation, conditional). Assume:

(T1) Cor3.12 A1-A3 hold (schema from task-377);
(T2) h_C equals the source normalized `-|log Θ|` under H1-H3;
(T3) Q_C is the normalized Q (Q_norm; no canonical d factor).

Then

    Q_C=-|log q|,  h_C=-|log Θ|,  Q_C<=h_C = P6.              (4.1)

Proof. Substitute T2/T3 into Cor3.12's `-|log q|<=-|log Θ|`. No explicit
complete C enters; the source schema is universal over admissible initial
data. QED.

Theorem 4.2 (canonical Q correction). If instead C9 uses Q_canon=C9Paper
QPaper, then under T1/T2:

    Q_canon <= d*h_C,   d=41,                               (4.2)

but Q_canon<=h_C is NOT derived. To recover P6 in the canonical convention,
one must convert either Q_canon/d or d*h_C and restate the target; mixing
conventions is invalid.

These two theorems exhaust the exact possibilities: either the normalized Q
is used and P6 follows exactly from Cor3.12 A1-A3, or the canonical Q is used
and the comparison carries the exact factor d=41.

## 5. What is exact, what is conditional, what is missing

EXACT/SOURCE:

- Cor3.12 uses normalized procession log-volumes -|log Θ|, -|log q|.
- C6 normalizedLogVolume is degree-normalized (1/D), not canonical.
- Canonical/normalized exact relation Q_canon=d Q_norm, d=41 in the tame
  C9 type; equality only d=1.
- If Q_norm is used and h_C=-|log Θ|, P6 follows from Cor3.12 A1-A3 without
  an explicit C.

CONDITIONAL:

- H1 C6 provenance/hull map;
- H2 procession pairing/weight equality;
- H3 B_I-zero arch normalization = source global log-volume normalization;
- choice of Q convention (normalized vs canonical) in the C9 target.

MISSING/EXACT GAPS:

- If C6 provenance/H1 is not the actual source map, h_C=-|log Θ| is not
  proved, even though both are normalized volumes.
- If the target insists on canonical QPaper Q, P6 must be restated with
  factor d; original canonical Q<=h_C does not follow.
- Actual procession weight identification ±j and B_I-zero global readout
  remain source-alignment conditions; no explicit completed C is required
  for the schema, but these alignments are needed to identify the quantities.

## 6. Factor audit summary

| quantity | source Cor3.12 | C9 candidate | exact relation |
|---|---|---|---|
| Θ hull volume | -|log Θ| normalized | C6 h_C normalized | h_C=-|log Θ| under H1-H3 |
| q-pilot | -|log q| normalized | PaperP6 Q_norm | Q_norm=-|log q| |
| q-pilot | -|log q| normalized | C9Paper Q_canon | Q_canon=d(-|log q|), d=41 |
| P6 target | -|log q|<=-|log Θ| | normalized h/Q | Q_norm<=h_C exact |
| P6 target | -|log q|<=-|log Θ| | canonical QPaper | Q_canon<=d h_C, not Q_canon<=h_C |
| procession | avg over F_l^× | C9 1/m avg, m=20 | equal by ±j pairing, no 1/2 |
| arch | source global log-volume | B_I-zero | equal under H3; shell-pi not used |
| C6 | normalized 1/D | C6 normalizedLogVolume | matches normalized side |

## 7. Conclusion

Cor3.12 A1-A3 give the universal normalized inequality
`-|log q|<=-|log Θ|`. C9 h_C matches the normalized `-|log Θ|` after the
C6/procession/B_I-zero alignment (H1-H3); C9 Q_C matches `-|log q|` exactly
only if the normalized PaperP6 qLog is used. If the canonical C9Paper QPaper
Q is used, the exact relation is `Q_canon=d*(-|log q|)` with d=41, so
Cor3.12 yields `Q_canon<=d*h_C`, not `Q_canon<=h_C`. Thus P6 true follows
exactly from A1-A3 in the normalized convention without constructing an
explicit C; in the canonical convention the factor d must be corrected and
the original canonical P6 is not the source inequality.

## 8. Status

Target-translation audit only. No black-box beyond the source schema; no
mixed/E3, no arbitrary data, no Lean/Project edits. Only this file written.
`target_accepted=false`; P6 exact in normalized convention conditional on
H1-H3, otherwise factor d corrected/open.
