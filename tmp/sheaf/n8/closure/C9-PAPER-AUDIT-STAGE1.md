# C9 paper audit: IUT III Corollary 3.12 (xi-d)-(xi-f)

## Scope

Audit C9Native.lean and C9Proof.lean QSigned/ThetaSigned/Values against the
paper. Paper source: papers/motizuki_corpus/text/Inter-universal Teichmuller
Theory III.txt. This is a paper-semantics audit, not a Lean-gap list. No
production edit.

## 1. Paper objects

### Theta(I)

Lines 10326-10338 define -|log(Theta)| in R union {+inf} as the
procession-normalized mono-analytic log-volume:
- procession-normalized, average over j in F_l^x (10329-10331);
- of the holomorphic hull (10332-10333);
- of the union of possible images of a Theta-pilot object (10333-10334);
- relative to the relevant Kummer isomorphisms (10336-10337);
- in the multiradial representation, subject to (Ind1),(Ind2),(Ind3)
  (10337-10338).

The proof repeats n,circ U as unions of possible Theta-pilot images, subject
to Ind1/2/3 (10359-10385), and n,circ U as their holomorphic hulls
(10386-10410). Compactness makes the quantity finite and negative in the
nontrivial branch (10408-10411).

### Q(I)

Lines 10340-10345 define -|log(q)| in R as the procession-normalized
mono-analytic log-volume:
- of the image of a q-pilot object (10341-10342);
- relative to the relevant Kummer isomorphisms (10342-10343);
- in the multiradial representation (10343-10344);
- NOT subject to (Ind1),(Ind2),(Ind3) (10344-10345).

The Delta label identification and |log q| > 0 are at 10345-10351.

Q is the q-pilot image region volume, not the Theta-image union volume.

### Values and R^{<= Theta}

Lines 10843-10849 define R^{<= -|log(Theta)|} = {lambda in R | lambda <=
-|log(Theta)|} and state -|log(Theta)| is the negative log-volume of 1,circ U,
while -|log(q)| is the log-volume of the q-pilot representation region.

Lines 10880-10887 state: the multiradial algorithm, hull formation and
log-volume yield a collection of possible log-volumes of pilot-object output
data R^{<= -|log(Theta)|} linked to the q-pilot log-volume.

Thus Values is a collection of possible pilot-object output log-volumes in
R^{<= Theta}; it is not a set of point log-degrees, and it is not defined as
Set.Iic Theta without the construction.

### Direction

Lines 10888-10898: construction of output possibilities is, perhaps only up to
approximation due to indeterminacies, a construction of -|log(q)|; the
inclusion -|log(q)| in R^{<= -|log(Theta)|} gives -|log(q)| <= -|log(Theta)|,
hence C_Theta >= -1. With Q = -|log(q)| and Theta = -|log(Theta)|, the
direction is Q <= Theta (also stated at 10351-10353).

## 2. Current definitions

C9Native.lean:
- QSigned (line 39): sourceSignedImageLogVolume v R n, i.e.
  -(sourceSetVolume (possibleThetaPilotImageSet v R n)).toReal.
- ThetaSigned (line 43): sourceSignedHullLogVolume v R n, i.e.
  -(sourceRealHullVolume v R n).
- Values (line 47): {z | exists y in SourceValues.values n x, z = -y}.
- ActualValuesBounded (line 52): forall z in Values, z <= ThetaSigned.
- ActualQApproximated (line 58): forall epsilon > 0, exists z in Values,
  QSigned - epsilon <= z.
- MissingSourceQHullComparison (line 66): forall n, QSigned n <= ThetaSigned n.

SourceValues.lean line 30:
values n x = {y | exists c : D.Choice n x,
  I.sourceLocalLogDegree D.place.v (D.eval n x c) = y}.

C9Proof.lean:
- line 47 proves ThetaSigned <= QSigned from hull containment;
- line 58 proves ThetaSigned <= every current Values element;
- line 91 equates QSigned <= ThetaSigned with hullVolume <= imageVolume;
- lines 158/163 leave target directions as attempts.

## 3. Correspondence

Theta(I): paper normalized hull of union of possible Theta images, Kummer,
Ind1/2/3 (10326-10338, 10359-10410). Current: raw -sourceRealHullVolume,
no procession average, no Kummer-relative log-volume, no Ind. Verdict: NOT
corresponding; only a raw value-layer hull volume.

Q(I): paper q-pilot image log-volume, Kummer, NOT Ind (10340-10345,
10846-10849). Current: -(Theta-image-union volume), i.e. the wrong region.
Verdict: NOT corresponding.

Values: paper possible output log-volumes in R^{<= Theta} (10843-10849,
10880-10887). Current: negatives of point log-degrees of C4 eval points.
Verdict: NOT corresponding; point degree is not an output-region log-volume.

Direction: paper Q <= Theta (10351-10353, 10895-10896). Current
ActualValuesBounded says point values <= Theta; C9Proof proves the reverse
inequalities for current definitions (lines 47,58). Verdict: NOT corresponding;
current Q/Values are mislabeled and the stated target is contradicted by the
current donors under finiteness.

+inf: paper allows -|log(Theta)| in R union {+inf} (10326-10328), proof splits
finite/negative (10354-10358). Current uses toReal, with top -> 0. Verdict:
NOT corresponding; +inf branch absent.

Ind asymmetry: paper Q not subject to Ind1/2/3 (10344-10345), Theta subject
(10337-10338). Current neither carries Ind operations. Verdict: NOT
corresponding.

## 4. Direction audit

Paper direction: Q <= Theta.

C9Proof line 47 proves ThetaSigned <= QSigned from hull containment. This is
the opposite direction and is decisive: current QSigned is the Theta-image
union, not the paper q-pilot region. C9Proof line 58 proves ThetaSigned <= z
for current Values; therefore ActualValuesBounded is not merely unproved but
contradicted by the current point-degree model. C9Proof line 91's equivalence
with hullVolume <= imageVolume is the reverse of the paper comparison because
current Q is the image-union volume. These are definition mismatches, not just
missing Lean lemmas.

## 5. Exact target corrections

C1. Define QPaper as the procession-normalized mono-analytic Kummer-relative
log-volume of the actual q-pilot image at (1,0) on 1,circ U_Q, with no Ind1/2/3
(10340-10345, 10846-10849). Required object: q-pilot region/log-volume from
source q data. Current possibleThetaPilotImageSet is the wrong region. If no
donor exists, exact missing type is qPilotRegion plus qPilotLogVolume.

C2. Define ThetaPaper as the procession-normalized mono-analytic log-volume of
the actual holomorphic hull 1,circ U of the union of possible Theta-pilot
images, Kummer-relative, subject to Ind1/2/3 (10326-10338, 10359-10410,
10846-10849). Current raw sourceRealHullVolume lacks procession average,
Kummer-relative normalization and Ind. Use C6 normalized volume plus actual Ind
data; do not add a new inequality.

C3. Define ValuesPaper from actual possible pilot-object output data/regions
after construction, hull, determinant and normalization: lambda equals the
signed normalized log-volume of an actual output. Paper 10880-10887 says this
collection is R^{<= Theta}. Do not use point log-degrees or Set.Iic Theta
without provenance.

C4. Restate q approximation per (xi-f) 10888-10894: construction of output
possibilities, perhaps only up to indeterminacy, constructs QPaper. Current
ActualQApproximated compares QSigned to point log-degrees; not the paper
statement.

C5. After C1-C3 prove QPaper <= ThetaPaper from QPaper in R^{<= ThetaPaper}
(10895-10896). Do not derive it from point-degree boundedness and do not use
MissingSourceQHullComparison as an input: it is the paper conclusion.

C6. Handle +inf separately (10326-10328, 10354-10358); current toReal top = 0
is wrong. Archimedean places are a separate source branch.

## 6. Verdict

Current C9Native/C9Proof QSigned, ThetaSigned, Values and ActualValuesBounded do
not correspond to the paper Q(I), Theta(I), Values and Q <= Theta:

- QSigned is a Theta-image-union volume, not the q-pilot image log-volume.
- ThetaSigned is a raw value-layer hull volume, not the normalized,
  Kummer-relative, Ind1/2/3 hull log-volume.
- Values are point log-degrees, not possible pilot-object output log-volumes.
- C9Proof proves the reverse inequalities; ActualValuesBounded is contradicted
  by the current donors.
- +inf and the Q/Theta Ind asymmetry are absent.

The paper target is QPaper <= ThetaPaper with ValuesPaper the possible output
log-volumes in R^{<= ThetaPaper}. C9 must be re-stated around these objects
before further conditional proof. Named sorrys are not the paper audit and do
not replace correcting the definitions.

## 7. Status

Paper lines cited: 10326-10358, 10359-10410, 10810-10831, 10832-10849,
10864-10898. Current definitions: C9Native:39,43,47,52,58,66;
SourceValues:30; C9Proof:47,58,91,149,158,163.

Conclusion: current definitions NOT paper-corresponding; exact corrections
C1-C6. No Lean statement is claimed valid by this audit; no production edit.
