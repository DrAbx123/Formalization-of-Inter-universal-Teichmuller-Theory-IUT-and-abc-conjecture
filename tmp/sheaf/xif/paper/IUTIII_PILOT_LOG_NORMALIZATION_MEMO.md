# IUT III qPilot / Θ-pilot log normalization — source audit memo

Date: 2026-10-30.
Scope: paper normalization only; no Lean edits, no compiled claims.
Primary sources: rendered PRIMS/arXiv pages from
tmp/external/promachina-iut-lean/docs/papers/mochizuki-iut-iii.pdf,
.../mochizuki-iut-iv.pdf, .../mochizuki-iut-ii.pdf, .../mochizuki-iut-i.pdf,
plus the OCR extract line numbers in tmp/source-extract/iut1.txt, iut2.txt,
iut3.txt, iut4.txt.

## 0. Verdict

1. qPilot log carries exactly a 1/(2l) factor relative to the classical
   q-parameter degree. The paper's q is the double-underlined q[2u], not the
   single-underlined q[1u]:

     |log q| = (1/(2l)) log(q).

   Here log(q) := deg(q_ADiv) is the classical q-parameter arithmetic degree
   (IUT IV p.23). Locally, the qPilot coefficient is ord_v(q[2u])
   (equivalently ord_v(q[1u])/(2l)), by IUT III p.124. There is no l factor and
   no separate degree factor beyond this 1/(2l).

2. qPilot log is a log-volume / arithmetic degree, not a bare order. Its local
   formula is ord_v(q[2u]) * log p_v; the global object is the
   procession-normalized mono-analytic log-volume of the image of the q-pilot
   object, and Proposition 3.9(iii) identifies such log-volumes with arithmetic
   degrees (up to the stated normalization). It is not ord_v(q[1u]).

3. Θ-pilot log is a hull log. It is the procession-normalized mono-analytic
   log-volume of the holomorphic hull of the union of possible images of the
   Θ-pilot object, subject to (Ind1),(Ind2),(Ind3). It is not the log-volume of
   the Θ-pilot object itself and not an average of theta-value magnitudes.

4. Cor 3.12 / Theorem B state

     -|log Θ| >= -|log q|   <=>   |log Θ| <= |log q| = deg(q)/(2l).

5. Citation correction: IUT III has only §§0-3. Definition 4.9 is IUT II,
   Definition 4.9(viii), not an IUT III definition. It defines the general
   pilot object (negative arithmetic degree) but gives no q/Θ-specific log
   formula.

## 1. Exact source passages

### 1.1 IUT I, Example 3.2(iv), p.71 (extract iut1.txt 3774-3788)

Page image confirms the typography:

- q_v with ONE underline: q[1u]_v, the classical q-parameter of E_v over K_v.
- q_v with TWO underlines: q[2u]_v, defined by

    q[2u]_v := q[1u]_v^(1/(2l))

  in O^tri(T_Xv), determined up to a mu_2l-multiple.
- The displayed formula is

    Θ_v(sqrt(-q[1u]_v)) = q[2u]_v.

This is the only place where the two q's are defined; all later q-pilot/theta
formulas inherit these underlines.

### 1.2 IUT III, Definition 3.8(i), p.112 (extract iut3.txt 6731-6769)

Page image (rendered p.112) shows the concrete q-pilot generator as

    "q[2u]_v",  v in V_bad,

with TWO underlines under q. The definition says:

- the Θ-pilot object is determined by generators up to torsion of the monoids
  Psi^perp_{F_lgp}(dagger HT^{Θ±ellNF})_v, indexed by v in V_bad;
- the q-pilot object is the object of the global realified Frobenioid
  dagger C^boxplus_Delta determined by generators up to torsion of the
  splitting monoid associated to the split Frobenioid dagger F^vdash_{Delta,v},
  concretely by the q[2u]_v, for v in V_bad, citing IUT I Example 3.2(iv).

Thus Definition 3.8(i) itself already selects the 2l-th root for the q-pilot
object.

### 1.3 IUT III, p.124 (extract iut3.txt 7601-7606)

Page image shows q with TWO underlines in both places:

    q := q[2u]_v,
    log(q) := ord_v(q[2u]_v) * log(p_v) in R.

This is the local qPilot logarithm. It is an order times log p_v, with the
order taken of q[2u], not q[1u].

### 1.4 IUT III, Theorem B, pp.21-22 (extract iut3.txt 1198-1229)

Theorem B defines:

- -|log Θ| in R union {+inf}: the procession-normalized mono-analytic
  log-volume (average over j in F_l^x) of the holomorphic hull of the union of
  the possible images of a Θ-pilot object, relative to the Kummer
  isomorphisms, in the multiradial representation of Theorems A, 3.11, subject
  to (Ind1),(Ind2),(Ind3).
- -|log q| in R: the procession-normalized mono-analytic log-volume of the
  image of a q-pilot object, relative to the same Kummer isomorphisms, in the
  multiradial representation, not subject to (Ind1),(Ind2),(Ind3).

Then:

    -|log Θ| in R,    -|log Θ| >= -|log q|,

i.e. C_Θ >= -1 for every C_Θ in R with -|log Θ| <= C_Θ * |log q|.

### 1.5 IUT III, Corollary 3.12, pp.173-174 (extract iut3.txt 10499-10529)

Same definitions as Theorem B. Page images confirm:

- the q in -|log(q)| has TWO underlines;
- the Θ side is explicitly the "holomorphic hull" of the "union of the
  possible images" of a Θ-pilot object, subject to (Ind1),(Ind2),(Ind3);
- the q side is the "image" of a q-pilot object, with no hull and no
  indeterminacies;
- the conclusion is

    -|log Θ| in R,    -|log Θ| >= -|log q|.

### 1.6 IUT IV, p.23 (rendered page image; extract iut4.txt 1351-1362, 1383-1388) — decisive

IUT IV defines the classical q-parameter degree

    log(q_v) := deg_{V(F_square)_v}(q^square_ADiv) in R_{>=0},
    log(q)   := deg(q^square_ADiv) in R_{>=0},

where q^square_ADiv is the effective arithmetic divisor determined by the
q-parameters of E_F at V(F_square)_bad. It then states explicitly:

  "the quantity '|log(q)| in R_{>0}' defined in [IUTchIII], Corollary 3.12,
   is equal to (1/(2l)) * log(q) in R [cf. the definition of 'q_v' in
   [IUTchI], Example 3.2, (iv)]."

This is an independent confirmation that the qPilot scalar is the classical
q-parameter degree divided by 2l, not the degree itself.

IUT IV p.30 (rendered page image; extract 1896-1897) repeats the same
normalization: "C_Θ * |log(q)|, i.e. the product of C_Θ and (1/(2l)) * log(q)".

### 1.7 IUT II, Definition 4.9(viii), p.158 (extract iut2.txt 10453-10468)

The general pilot object associated to an F^boxplus-blacktriangleright-times-mu-
prime-strip:

- generators of the monoids O^blacktriangleright(-) at v in V_bad, together
  with {rho_w}_{w in V}, determine a well-defined object, up to isomorphism, of
  the global realified Frobenioid C^boxplus of negative arithmetic degree;
- this object is called the pilot object.

No q/Θ-specific formula, no 1/(2l), and no hull appear here. This is why
Definition 4.9 alone cannot settle the normalization; the exact formulas are in
Definition 3.8(i), p.124, Theorem B, Cor 3.12, and IUT IV p.23.

### 1.8 Supporting normalization statements

- IUT III, Proposition 3.9(iii), p.117 (extract 7082-7091): the global
  log-volume mu^log_{A,V_Q}(J) is equal to the degree of the arithmetic line
  bundle determined by J, relative to a suitable normalization. Thus
  "qPilot log = arithmetic degree" is a theorem-level interpretation, not a
  separate definition.
- IUT III, Remark 3.1.1(ii), pp.94-95 (extract 5504-5537): the local weights
  are 1/[K_v:(F_mod)_v], normalized so that multiplication by p_{v_Q} adds
  log(p_{v_Q}). These weights are attached to the local log-volumes of
  Remark 3.1.1(ii); they are local degree weights, not a global l or 2l factor.
- IUT III, Proposition 3.9(i), pp.115-116 (extract 6969-7011): the
  procession-normalization is the average over the capsules/labels. For the Θ
  side the average is over j in F_l^x, i.e. weight 1/|F_l^x| = 1/(l-1) (or
  1/l* on the sign classes j=1,...,l*, if signs are identified). This is an
  average, not a multiplicative l factor.

## 2. Exact formulas

Let

    q[1u]_v := q-parameter of E_v/K_v,    q[2u]_v := q[1u]_v^(1/(2l)).

### 2.1 qPilot

    |log q| = (1/(2l)) log(q),

where log(q) = deg(q_ADiv) is the classical q-parameter arithmetic degree
(IUT IV p.23). Locally, the coefficient is

    c_v^qPilot = ord_v(q[2u]_v) = ord_v(q[1u]_v)/(2l)

(IUT III p.124). It is not c_v = ord_v(q[1u]_v). The Remark 3.1.1(ii) weights
w_v = 1/[K_v:(F_mod)_v] are attached to the local log-volumes; they do not add
an l or 2l factor. The sign is negative: -|log q| is the log-volume of the
q-pilot image.

### 2.2 Θ-pilot

    -|log Θ| = procession-normalized mono-analytic log-volume(
                 hull( union of possible images of the Θ-pilot object ) ),

subject to (Ind1),(Ind2),(Ind3). The theta values are

    theta_v(j) = q[2u]_v^(j^2) = q[1u]_v^(j^2/(2l)),  j=1,...,l*,

up to mu_2l. This theta-value formula is input data for the hull;
-|log Θ| is not the average of the numbers log theta_v(j).

### 2.3 Inequality

    -|log Θ| >= -|log q|   <=>   |log Θ| <= |log q| = deg(q)/(2l).

This is the precise content of Cor 3.12 / Theorem B. It is a non-strict
inequality; no equality is asserted.

## 3. Answers to the three questions

| question | answer |
|---|---|
| Is there a degree factor? | The qPilot scalar is an arithmetic degree divided by 2l: |log q| = deg(q)/(2l). The Θ scalar is a hull log-volume, not a degree. |
| Is there an l factor? | No multiplicative l factor. The Θ side has the procession average over j in F_l^x (weight 1/(l-1), equivalently 1/l* on sign classes), which is an average, not an l multiplier. |
| Is there a 2l factor? | Yes, exactly one: qPilot is 1/(2l) of the classical q-parameter degree, equivalently it uses q[2u]=q[1u]^(1/(2l)). The theta values carry the same root: exponent j^2/(2l) relative to q[1u]. |
| Is qPilot "order"? | Locally its coefficient is ord_v(q[2u]), not ord_v(q[1u]). Globally it is a log-volume/arithmetic degree, not a bare order. |
| Is Θ "hull log"? | Yes: the log-volume of the holomorphic hull of the union of possible images, subject to (Ind1),(Ind2),(Ind3). Not the Θ object's own log-volume and not a theta-value average. |

## 4. Conflict with existing memos (must be resolved)

Two existing project memos reach opposite conclusions:

1. tmp/sheaf/xif/paper/QPilotThetaRootNormalizationSourceAudit.md §§3-6:
   q-pilot uses the root q[2u]; |log q| = (1/(2l))|log q_param|.
   This agrees with the rendered pages and with IUT IV p.23.
2. tmp/sheaf/xif/paper/RootFactorQThetaCoefficientAnalysis.md §§1.2, 4-5:
   claims the q-pilot uses the classical q[1u] and that "no factor 1/(2l)
   belongs to the paper q-pilot scalar"; it calls the root-normalized scalar
   "auxiliary, not the paper q-pilot scalar".
   This contradicts:
   - the double underline on the q-pilot q_v in Definition 3.8(i), p.112;
   - the double underline on the q in p.124 and Cor 3.12, p.174;
   - IUT IV p.23, lines 1383-1388, which explicitly says
     |log q| = (1/(2l)) log(q).

   Its source citation to Definition 3.8(i) appears to rely on OCR, which loses
   the underlines (NOTATION_Q_UNDERLINES.md warns about exactly this). It should
   be corrected, not used for the qPilot target.

AUDIT_CANONICAL.md is ambiguous: line 59/68 says "q-pilot log is
ord_v(q_v)*log(p_v) (classical q-pilot log)", but it does not say whether that
q_v is q[1u] or q[2u]. Given IUT IV p.23, the paper qPilot is the q[2u]
version; the phrase "classical q-pilot log" should be reserved for the q[1u]
auxiliary scalar and must not be identified with the paper -|log q|.

## 5. Lean audit (read-only; no edits, no compile)

The following are source-level observations, not compiled claims.

### 5.1 qVFamily is q[1u]

tmp/sheaf/xif/paper/QVFamRootFactorCorrectionActual.lean lines 9-14:

  "q_v is the classical q-parameter; q_v^(1/2l) is the chosen 2l-th root; ...
   The value qVFamily T b is the classical q parameter (order = qVFamily.order)."

This is consistent with qVFamPaperRootCoefficient = order/(2l) (lines 56-57)
and qVFamTensorCoefficient = (2l) * qVFamPaperRootCoefficient (lines 66-72).
So qVFamily is q[1u], not q[2u].

### 5.2 qPilotClassicalLog is 2l times the paper qPilot

tmp/sheaf/xif/paper/QPilotClassicalLogActual.lean lines 31-35 defines

    qPilotClassicalLog = sum_b ord(qVFamily_b) * log(residueNormBase_b).

Since qVFamily is q[1u], this is the classical q[1u] scalar, i.e. 2l times the
paper |log q| (up to the same local-degree normalization). It should not be
called the paper qPilot log.

### 5.3 RootCorrectedQPilotScalarActual has the paper scalar, but mislabels it

tmp/sheaf/xif/paper/RootCorrectedQPilotScalarActual.lean lines 54-71 and
113-128 construct

    qVPilotRootNormalizedMagnitude = classical magnitude / (2l),
    qVPilotRootNormalizedSignedLogVolume = -qVPilotRootNormalizedMagnitude.

This is the paper qPilot scalar (up to weights). But its lines 143-156 call
qPilotPaperCoefficient = order(qVFamily) the paper coefficient and label the
root coefficient "auxiliary, not the paper q-pilot coefficient". Per IUT IV
p.23 this labeling is backwards: the root-normalized scalar is the paper one;
the classical order is the auxiliary (q[1u]) scalar.

### 5.4 S695 / S705 / S714 use the classical q[1u] coefficient

- S695QPilotNormalizationAuditActual.lean lines 7-9: "Paper q-pilot log
  coefficient: ord_v(q_v), no extra degree or 2l factor." This is true only for
  q[1u]; it is false for the paper q[2u] q-pilot.
- S705QPilotThetaFormulaAuditActual.lean lines 6-8: same claim
  qPilot = sum w_v * ord_v(q_v) * log p_v; the same correction applies.
- S714HullComparisonActual.lean lines 60-63: paperQPilotMagnitude =
  order(qVFamily) * log p; this is 2l times the paper qPilot magnitude.

### 5.5 BadPlaceProcessionNormalizedComparisonActual is asymmetric

BadPlaceProcessionNormalizedComparisonActual.lean lines 55-66 defines

    qPilot = sum_b w_b * c_norm * log p_b,
    Theta  = sum_b w_b * (c_norm/(2l)) * log p_b.

Only the Θ side is divided by 2l. If c_norm is the q[1u] coefficient, then the
Θ scalar is numerically the paper qPilot scalar, while the qPilot scalar is 2l
times the paper one; the resulting comparison is not the paper Cor 3.12
comparison. If both sides are expressed in q[1u], the paper comparison has
c_norm/(2l) on the qPilot side and j^2 c_norm/(2l) (hull-normalized) on the Θ
side; if both are expressed in q[2u], the qPilot coefficient is c_norm and the
theta coefficient is j^2 c_norm. Dividing only one side by 2l is not
paper-faithful.

### 5.6 The hull model

S707ThetaHullVsThetaValueActual.lean correctly records that -|log Θ| is a hull
log-volume, not a theta-value average (lines 4-12, 28-44). But
S663ActualAverageNormalizedHaarActual.lean lines 110-128 builds s663Average
from rootThetaMagnitudeProcession T b, i.e. a theta-magnitude procession, and
uses it as the target average of PaperSignedHull. That is a theta-value
surrogate, not the paper's holomorphic hull of the union of possible images
under (Ind1),(Ind2),(Ind3). The actual hull-of-union construction remains the
G4/G5 gap in AUDIT_CANONICAL.md.

### 5.7 The c_norm target is conditional

PaperLevelXiFTargetProofActual.lean lines 56-105 builds perBQPilotLog from
rootNormCoefficient, which S736RootNormCoefficientAuditActual.lean lines 7-13
identifies as the generator-supply spectral coefficient, not necessarily
order(qVFamily). Therefore:

- if c_norm = order(qVFamily), that qPilot scalar is 2l times the paper qPilot;
- if c_norm is a different spectral coefficient, its relation to the paper
  q-parameter degree is the exact S736PaperOrderGap and must be established
  before claiming Cor 3.12.

Either way, the current target cannot be declared paper-faithful without
settling this point.

## 6. Verification status and next actions

Verified from rendered page images:
- q[1u] vs q[2u] underlines in IUT I p.71, IUT III pp.112, 124, 173-174;
- IUT IV p.23 and p.30: the displayed factor is 1/(2l) * log(q);
- Cor 3.12 / Theorem B wording (hull, union of possible images, Ind1-3; q side
  image only, no Ind1-3);
- IUT IV p.23 lines 1383-1388: |log q| = (1/(2l)) log(q);
- IUT II p.158 Definition 4.9(viii): pilot object of negative arithmetic
  degree, no q/Θ formula.

Verified from OCR extract text (line numbers above): the surrounding prose and
the exact inequality signs.

Not verified / not claimed:
- no Lean compilation was run;
- no claim that c_norm = order(qVFamily) (S736 says this is an exact gap);
- no claim that the current PaperSignedHull/s663Average is the paper hull; it is
  a theta-value surrogate;
- no claim of equality in Cor 3.12.

Recommended next actions:
1. Use the root qPilot scalar in the paper target. Either use
   qVFamPaperRootCoefficient = order/(2l) (or the existing
   qVPilotRootNormalizedSignedLogVolume) as the qPilot scalar, or prove an exact
   source identification that the paper q-pilot generator is q[2u] and that the
   classical q[1u] scalar is not the target.
2. Keep the theta coefficient j^2 * order/(2l). It is the correct theta-value
   coefficient relative to q[1u]; do not replace it by j^2 * order.
3. Fix the labels/docstrings in S695, S705, S714,
   RootFactorQThetaCoefficientAnalysis.md, and
   RootCorrectedQPilotScalarActual.lean so that the classical q[1u] scalar is
   marked auxiliary and the root q[2u] scalar is marked paper.
4. Re-state Cor 3.12 with the factor: |log Θ| <= |log q| = deg(q)/(2l).
   Do not state |log Θ| <= order(qVFamily)*log p as the paper inequality.
5. Keep the hull-of-union as a separate exact object. The current
   theta-magnitude procession is not the paper hull; the actual
   (Ind1),(Ind2),(Ind3)-union hull is still the G4/G5 gap.
6. If the project wants to keep the classical q[1u] scalar as an auxiliary
   "2l-scaled" model, name it explicitly (e.g. classicalQPilotLog) and prove the
   exact relation classicalQPilotLog = 2l * |log q|. Do not identify it with
   the paper -|log q|.

## 7. One-line summary

Paper normalization is:

    |log q| = (1/(2l)) deg(q),
    local coefficient c_v^qPilot = ord_v(q[2u]_v) = ord_v(q[1u]_v)/(2l),

and

    -|log Θ| = procession-normalized log-volume of the holomorphic hull of the
               union of possible Θ-pilot images (Ind1-3),

with

    -|log Θ| >= -|log q|.

No extra l factor; exactly one 1/(2l) on the qPilot side.

## Appendix: page images used (workspace paths)

- IUT I p.71: tmp/pdf-render-v/iut1-p071.png
  (detail crops: tmp/pdf-render-v/iut1-textq-wide.png,
   tmp/pdf-render-v/iut1-leftq-wide.png, tmp/pdf-render-v/iut1-rightq-wide.png)
- IUT III p.112 (Def 3.8(i)): tmp/pdf-render-v/iut3-p112.png
  (detail: tmp/pdf-render-v/iut3-defq-wide.png)
- IUT III p.124 (log(q)): tmp/pdf-render-v/iut3-p124.png
  (detail: tmp/pdf-render-v/p124-assign.png, p124-logformula.png)
- IUT III p.21-22 (Theorem B): tmp/pdf-render-v/iut3-p021.png
- IUT III p.173-174 (Cor 3.12):
  tmp/pdfs/source-audit-20260804/iut3/p173-173.png,
  tmp/pdfs/source-audit-20260804/iut3/p174-174.png
  (detail: tmp/pdf-render-v/p174-logq.png, p174-qpilot.png)
- IUT III p.183 (xi-d): tmp/pdfs/source-audit-20260804/iut3/p183-183.png
- IUT IV p.23, p.30:
  tmp/pdf-render-v/iut4-p023.png, tmp/pdf-render-v/iut4-p030.png
- IUT II p.158 (Def 4.9(viii)): tmp/pdfs/iut-ii-def-4-9-158.png

The OCR extract files are text-only and lose the underlines; the page images
above are the authority for q[1u] vs q[2u].
