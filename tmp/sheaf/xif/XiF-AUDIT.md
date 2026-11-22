# XiF xi-f source-fidelity audit

Task: task-491. Date: 2026-10-28. Author: transport.
Audit of tmp/sheaf/xif/SourceXiFConstruction.lean against IUT III xi-d/e/f.
No Lean edits; no target substitution. Only this file and the ledger append.

## 0. Input and compile evidence

| item | value |
|---|---|
| Lean source | tmp/sheaf/xif/SourceXiFConstruction.lean |
| lines | 129 |
| SHA256 | FAD7464664F5BBA3C7EDA814416F4E3E74C3045060ABCE589514084A9476A146 |
| compile command | cd D:\lean; lake env lean -j1 -R 'D:\lean' 'tmp\sheaf\xif\SourceXiFConstruction.lean' |
| exit code | 0 |
| stdout/stderr | empty |

The file itself has no sorry, axiom, or admit. Its theorem names:

- sourceQPilotPoint
- sourceQPilotLogVolume
- sourceThetaHullLogValueSet
- sourceThetaHullLogVolume
- sourceQPilotPoint_mem_hull
- sourceQPilotLogVolume_mem_valueSet
- sourceQPilotLogVolume_eq_gauss
- sourceXiFInclusion_of_bounded
- sourceThetaHullLogValueSet_bddAbove_of_contracted
- sourceXiFInclusion

These compile. Compilation proves the Lean objects exist and the stated
theorems typecheck. It does not prove that the objects are the paper objects.

## 1. Paper anchors

IUT III local text: tmp/sheaf/n8/closure/sources/IUT-III.txt,
SHA256 822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D.

### xi-a (lines 10571-10581)

Consider a q-pilot object at (1,0), interpreted relative to the 1-column
holomorphic log-shells.  The Theta x mu LGP-link from (0,0) to (1,0) relates the
Theta-pilot object at (0,0) to the q-pilot object at (1,0).

Paper objects: a q-pilot object at (1,0), a Theta-pilot object at (0,0), and the
LGP-link between the two columns.  The q-pilot is not a theta value at label 1.

### xi-d (lines 10641-10681)

The source applies determinant and normalized log-volume to:

    the region 1,circ U
and
    the region that arises from the representation of the q-pilot object at
    (1,0) on 1,circ U_Q,

both in 1,circ U_Q.  It obtains the comparable objects

    R_{<= -|log(Theta)|}
and
    -|log(q)|.

Here -|log(Theta)| is the procession-normalized mono-analytic log-volume of
the holomorphic hull of the union of possible Theta-pilot images, and -|log(q)|
is the log-volume of the q-pilot region.  The paper uses the determinant
comparison to put them in the same normalized scale.

### xi-e (lines 10682-10704)

Expressibility relative to the 1-column arithmetic holomorphic structure amounts
to operations valid under the condition that the pilot-object log-volume
associated to the input data prime-strip be the fixed value -|log(q)|.

### xi-f (lines 10705-10715)

The construction of possible output log-volumes constitutes a construction of
the input q-pilot log-volume, perhaps only up to indeterminacies; hence

    -|log(q)| in R_{<= -|log(Theta)|},
    -|log(q)| <= -|log(Theta)|.

This is a statement about the q-pilot output log-volume and the Theta-hull
output-log-volume class, not about a pointwise local log-degree of a theta
label.

## 2. What the Lean file constructs

### 2.1 sourceQPilotPoint

    def sourceQPilotPoint (v : V) (R : I.SourceImageRealization v)
        (n : ThetaPilotCarrier l) : I.ThetaPilotPoint v :=
      I.sourceThetaPilotPoint v R n (oneSignedLabel (l := l))

This is the Theta-pilot value point at the signed label j=1.  It is not the
paper q-pilot object at (1,0), and no source anchor identifies the q-pilot with
the theta-pilot label-1 point.

### 2.2 sourceQPilotLogVolume

    def sourceQPilotLogVolume ... : Real :=
      I.sourceLocalLogDegree v (I.sourceQPilotPoint v R n)

The theorem sourceQPilotLogVolume_eq_gauss gives:

    sourceQPilotLogVolume v R n =
      (Fintype.card (SourceVolumeIndex l) : Real) *
        Real.log ((I.theaterAt 0 0).thetaPacket.q).

For l=41, SourceVolumeIndex has cardinality (lStar+1)*l = 21*41 = 861.  Thus
this Lean quantity is 861 * log(q), not the paper value -|log(q)|.  Unless a
separate normalization identifies the cardinality factor and the sign with the
paper q-pilot log-volume, the numerical object is not the paper q-pilot
log-volume.

### 2.3 sourceThetaHullLogValueSet and sourceThetaHullLogVolume

    def sourceThetaHullLogValueSet ... : Set Real :=
      I.sourceLocalLogDegree v '' (I.sourceHolomorphicHull v R n : Set ...)

    def sourceThetaHullLogVolume ... : Real :=
      sSup (I.sourceThetaHullLogValueSet v R n)

This is the supremum of the pointwise local log-degrees of points in the
value-monoid holomorphic hull.  It is not the paper's procession-normalized
mono-analytic log-volume of the 1,circ U holomorphic hull.  The supporting Lean
file CardHullRealGeneratorNonpositivity explicitly describes its construction
as the value-layer form of [AbsTopIII] Proposition 5.7, not the paper's
1,circ U carrier.

### 2.4 sourceXiFInclusion

    theorem sourceXiFInclusion ... (hq : q <= 1)
        (hScaling : forall s in sourceScalingUnits, sourceLocalLogDegree s <= 0) :
        sourceQPilotLogVolume v R n <= sourceThetaHullLogVolume v R n

The proof is: the q-pilot point is in the hull (tautologically, because it is a
Theta point at label 1); the hull's pointwise log-degrees are bounded above by
0 under hq/hScaling; hence the q-point log-degree is at most the supremum.

This is a pointwise value-layer inequality.  It is not the paper xi-f
membership

    -|log(q)| in R_{<= -|log(Theta)|}

and it is not even a statement about the same q-pilot log-volume, for the
reasons in 2.1-2.3.

## 3. Per-step source-fidelity verdicts

### q-pilot-as-label-1

VERDICT: REJECT as paper xi-f.

- Paper q-pilot: q-pilot object at (1,0), determined by q_v and its
  arithmetic line bundle/Frobenioid data (Def3.8(i), xi-a).
- Lean object: Theta-pilot point at signed label j=1.
- No source theorem identifies these.  The name sourceQPilotPoint is a concept
  substitution, not a proof.

### q-pilot log-volume

VERDICT: REJECT as paper -|log(q)|.

- Paper: -|log(q)| is the log-volume of the q-pilot region (xi-d).
- Lean: card * log(q), with card=861 for l=41.
- The factor 861 is not a paper normalization; no theorem in the file removes
  it or identifies it with the paper value.  SourceQPilotLogVolume_eq_gauss is
  an exact Lean identity for the constructed point, not for the paper q-pilot.

### Theta-hull log-volume

VERDICT: REJECT as paper -|log(Theta)| (value-layer surrogate only).

- Paper: procession-normalized mono-analytic log-volume of the holomorphic hull
  of the possible Theta-pilot images in 1,circ U.
- Lean: sSup of sourceLocalLogDegree over the value-monoid hull.
- The value-monoid hull is not the paper's IQ/log-shell hull; the file's own
  supporting module says it is a value-layer form, not the paper carrier.
- sSup of point log-degrees is not the paper hull log-volume; the paper hull
  volume is a normalized Haar/log-volume of a region, not a supremum of
  pointwise local degrees.

### xi-f inclusion

VERDICT: REJECT as paper xi-f.

- Paper: -|log(q)| is a possible output log-volume, hence lies in
  R_{<= -|log(Theta)|}; this uses the xi-d determinant comparison and the
  xi-e/f construction-computation.
- Lean: q-point log-degree <= sup of hull point log-degrees, from hull
  membership and boundedness.
- This is a much weaker pointwise statement.  It does not assert the paper
  q-pilot log-volume, does not assert membership in R_{<= -|log(Theta)|}, and
  does not use the determinant/log-volume comparison.

### Remaining hypotheses

The Lean theorem sourceXiFInclusion depends on:

(Hq) q <= 1;
(HScaling) every source scaling unit has sourceLocalLogDegree <= 0.

Hq is consistent with the paper q-parameter having |q|<1 only after a separate
normalization; it is not derived from the paper q in this file.  HScaling is a
substantive contraction hypothesis on the value-layer scaling units; it is not
a paper xi-f hypothesis.  The boundedness theorem
sourceThetaHullLogValueSet_bddAbove_of_contracted depends on both.

The paper xi-f hypotheses are the initial Theta-data, the multiradial
construction, the determinant/log-volume comparison, and the fixed q-pilot
value.  The Lean file replaces these with a value-layer point, a pointwise
supremum, and the Hq/HScaling contraction conditions.  Those are not the same
hypotheses.

## 4. Paper conditions versus constructed Lean objects

| paper condition/object | Lean object in SourceXiFConstruction | status |
|---|---|---|
| admissible initial Theta-data C | source OriginalInput abstraction | paper condition, not constructed |
| q-pilot object at (1,0) | sourceQPilotPoint = Theta point label 1 | NOT the paper object |
| -|log(q)| q-pilot log-volume | card * log(q) local log-degree | factor/sign mismatch |
| Theta-pilot possible images / holomorphic hull in 1,circ U | value-monoid sourceHolomorphicHull | value-layer surrogate |
| -|log(Theta)| procession-normalized hull log-volume | sSup of pointwise log-degrees | different construction |
| determinant / O(-) / normalized log-volume comparison | not present | missing |
| Ind1/Ind2/Ind3 | not represented in this file | missing |
| xi-e fixed q-pilot value | not used | missing |
| xi-f membership in R_{<= -|log(Theta)|} | pointwise q-point degree <= hull sup | different statement |

## 5. Exact obstruction / counterexample

The file cannot be used as a paper-level xi-f construction for at least three
independent reasons:

(O1) Object mismatch: sourceQPilotPoint is a Theta point at label 1, not the
     q-pilot object.  No source anchor identifies them.

(O2) Numerical mismatch: sourceQPilotLogVolume = card * log(q) = 861 log(q)
     for l=41, while the paper q-pilot log-volume is -|log(q)|.  Unless a
     separate normalization theorem identifies these, the Lean theorem is
     about a different real number.

(O3) Statement mismatch: sourceXiFInclusion is a pointwise inequality of local
     log-degrees on a value-monoid hull, not the membership of the q-pilot
     log-volume in the possible-output-log-volume set R_{<= -|log(Theta)|}.
     It also assumes hScaling, which is not a paper xi-f condition.

The Lean theorem sourceXiFInclusion is true for its own value-layer objects and
does not assert a false paper statement.  It is a surrogate construction, not a
source-faithful construction of xi-f.

No arbitrary data or target substitution is introduced by this audit.  The
audit does not edit or weaken the Lean file.

## 6. What would be needed for paper-level xi-f

A paper-level Lean construction would need:

1. the actual q-pilot object at (1,0), not a Theta label-1 point;
2. its actual normalized log-volume -|log(q)|, not card * log(q);
3. the procession-normalized log-volume of the actual 1,circ U hull, with
   the determinant/O(-) comparison and Ind1/Ind2/Ind3;
4. the xi-e fixed-value interpretation and the xi-f inclusion;
5. no hScaling substitute for the paper's compactness/log-volume argument.

None of 1-5 is present in SourceXiFConstruction.lean.

## 7. Status

- SourceXiFConstruction.lean compile: EXIT0.
- Its Lean theorems are valid for the constructed value-layer objects.
- Paper-level xi-f: NOT constructed.
- Audit verdict: REJECT source fidelity; retain as value-layer conditional
  surrogate only.

target_accepted=false.
