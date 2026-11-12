# S1487: O-layer q-pilot scalar equality on the concrete Gaussian C3

Date: 2026-10-31
Lean: `tmp/sheaf/xif/paper/S1487OQPilotScalarEqualityActual.lean` (776 lines)
EXIT=0 (source compile and `.olean` build)
SHA256(source) 4A0D0DAFB50D91E118D3F1B32D3BF127CC9812059338BFD7CB8FE0243A309177
olean: `D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1487OQPilotScalarEqualityActual.olean`
olean bytes: 591240; olean mtime 2026-10-31T02:25:16+08:00
Axioms (8 probes): only `propext`, `Classical.choice`, `Quot.sound`.  No `sorry`/`admit`/new axiom.

Build command: `lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1487OQPilotScalarEqualityActual.olean tmp/sheaf/xif/paper/S1487OQPilotScalarEqualityActual.lean` (EXIT=0).  The olean was re-imported by a scratch module to confirm it loads.

## Target

S1463 field `scalar_eq : O.qPilotLogVolume = OrigXiFPaperQPilotLogVolume C3`; since
`O.qPilotLogVolume = sourceQPilotSignedLog I.initial` (object field) and
`OrigXiFPaperQPilotLogVolume C3 = -|log ||C3.q.q|||`, this is, definitionally,

  `sourceQPilotSignedLog I.initial = -|Real.log ||C3.q.q|||`

on the concrete Gaussian C3 (`S1391 actualSourcePilotRegionDataL`, S1438
`OrigXiFPaperQPilotFromSourceLActual` attachments).  No use of the target
proposition as input.

## What is proved

### 1. Arithmetic evaluation of the actual single completion q

Concrete Gaussian place over 5: `S1487FivePlace : FinitePlaceAtPrime GaussianField 5`
(`concreteGaussianFivePlace`, rational prime 5 by `concretePlace_rationalPrime_eq_five`).
Actual q candidate `S1487Cand`.

* `S1487_residueNormBase_five : residueNormBase S1487FivePlace.val = 5`
  (from the actual residue field `ZMod 5` of the chosen place).
* `S1487Cand_magnitude : localLogMagnitude S1487Cand = (order : ℝ) * Real.log 5`
  (Mathlib arithmetic completion norm, `ArithmeticQPilotBaseChange`).
* `S1487Cand_magnitude_pos`, `S1487Cand_magnitude_ge_log_five : log 5 <= localLogMagnitude`.

Consequently the single-q side of the paper scalar is `-order * log 5`, with
`order >= 1`, i.e. strictly negative and at most `-log 5`.

### 2. An actual concrete `OriginalInput l (FinitePrimePlace 2 7)`

The tree contains no such inhabitant (Example36 records the D-prime-strip
Galois card).  §2 constructs one: the explicit shear family
`Int x Int -> HodgeTheater l (FinitePrimePlace 2 7)` (shear matrix
`[[1+nm,n],[m,1]]`, injective, links and their refl/symm/trans laws,
permutation naturality), specialised from the model already used by
`SourceUnitRegionHaarDataActual`; arithmetic alignment is `rfl`.  This is a
genuine `SourceHodgeTheaterFamily`/ `OriginalInput`, not an arbitrary
inhabitant: every field is constructed.

### 3. Legitimate Definition 3.1 source data over the concrete Gaussian arithmetic

`S1487SourceData Bad [Fintype Bad] q ...` builds a literal
`SourceDefinition31Data.{0} l` with Gaussian arithmetic, the bad family `Bad`,
and the explicitly supplied q-parameters (nonzero, contracting, `!= 1`).  The
torsion/orbicurve/section/cusp clauses are filled with explicit carriers (they
are irrelevant to the scalar); their content is explicitly **not** claimed to
be the paper's D5-D9 data.  The scalar conclusions use only the bad-place
clause and the actual completion q.

### 4. TRUE branch: the equality holds for the faithful one-place datum

Bad family `PUnit`, q-parameter = the actual completion magnitude `||q||`:

* `S1487Faithful_sourceBadQAbsLog : sourceBadQAbsLog = localLogMagnitude S1487Cand`
* `S1487FaithfulScalarEq : OrigXiFPaperQPilotScalarExactFirstField ...`
* `S1487_origXiFScalarExactField_faithful`: the S1463 `scalar_eq` field holds
  for **every** `PaperQPilotObject` over this input and C3.

So the equality is not vacuous: for a one-place family whose q is the actual
completion q it is true.

### 5. FALSE branch (actual counterexamples)

(a) **Two bad places, both with the actual completion magnitude**:
`S1487TwoPlace_sourceBadQAbsLog = 2 * localLogMagnitude S1487Cand`, while the
single completion q contributes `-localLogMagnitude`; hence
`S1487TwoPlaceScalarNe : ¬ OrigXiFPaperQPilotScalarExactFirstField`.  The
bad-family sum double-counts the single completion q.

(b) **Explicit rational q-parameters `1/2` on two bad places** (no dependence
on the value of `order`):
`S1487Half_sourceBadQAbsLog : sourceBadQAbsLog = Real.log 4`,
single-q side `<= -Real.log 5`, and `log 4 < log 5`; hence
`S1487HalfScalarNe : ¬ OrigXiFPaperQPilotScalarExactFirstField`.

(c) O layer: `S1487_no_origXiFScalarExactField` — for **every**
`PaperQPilotObject O` over the two-place input,
`¬ OrigXiFThetaLinkActualScalarExactField O S1487TwoPlaceC3`.  Hence no
`OrigXiFThetaLinkActual` inhabitant exists at that concrete I and C3: S1463's
`scalar_eq` is false, not merely unproved, at this data.

## Exact reductions used (imported, not reproved)

* `OrigXiFPaperQPilotScalarExactFirstField C3 ↔ -sourceBadQAbsLog = -|log ||C3.q.q|||`
  (`OrigXiFPaperQPilotScalarActual`).
* `OrigXiFThetaLinkActualScalarExactField O C3 = (O.qPilotLogVolume = paper scalar)`
  and `O.qPilotLogVolume = sourceQPilotSignedLog I.initial` (S1463).

## Scope, caveats, next step

* The Gaussian C3 side is the actual S1391 record at the concrete Gaussian
  place above 5; the norm and residue computations are Mathlib-arithmetic, not
  normalized/native data.
* The two/three-place source data are legitimate models of the Definition 3.1
  contract but not the paper's D5-D9 data (which the tree does not possess).
  They show the scalar equality is **not a consequence of the contract** and
  can be **false**; they do not decide the value at the still-hypothetical
  S1280 actual Gaussian datum.
* For the S1280-style actual Gaussian datum (singleton bad family at the place
  above 5, q-parameter `5^{-order}`) the equality reduces by
  `S1487_residueNormBase_five` and the order formula to
  `order_bad * log 5 = order_C3 * log 5`, i.e. to `order_bad = order_C3`.
  No inhabitant of that datum exists in-tree (D5-D9 cards), so that concrete
  numerical equality is not decided here; it is the precise remaining
  arithmetic statement if the S1280 datum is the intended I.
* Nothing is claimed about the signed-hull second field.
