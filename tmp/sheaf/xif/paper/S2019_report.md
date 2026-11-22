# S2019: the root stackification rebased on the corrected full property

File: `tmp/sheaf/xif/paper/S2019RebasedRootStackActual.lean`
SHA-256 (lean): 12ECE7DFA9FC38CC87448DBF26084F78316CAC3E28CF17D56D4922597BEE5F8C
EXIT: 0  (no warnings, no sorry/admit/new axiom)
Olean: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S2019RebasedRootStackActual.olean`
SHA-256 (olean): 152FA55D6470DD2EA2B63FEEAE68374FF89A18C001AC47553875AD2D9146DA02
Consumer check: `_S2019Consumer.lean` EXIT=0 (imports the olean).
Axioms: every `#print axioms` block is {propext, Classical.choice, Quot.sound}.

## What is defined

* `S2019IsoCommaDescent F R`: the corrected full descent datum at a sieve,
  in the actual iso-comma form of S2015's `S2015FullPullback` (exists_lift +
  unique_lift up to isomorphism).
* `S2019FullIsStack F`: prestack + corrected full descent at every covering
  sieve -- the stack condition rebased on S2015's corrected full 2-universal property.
* `S2019RootFullDescentAll` / `S2019RootFullIsStack` / `S2019FirstMissing`:
  the correction specialised to `S1997RootPrestack K l`, and the named exact first
  missing in corrected form.
* `S2019CorrectedIdentityPresentation` / `S2019CorrectedFiniteEtale` /
  `S2019CorrectedFiniteEtaleAll`: S2015's corrected base-change data for the
  covers (definitionally S2015's `S2015CorrectedRepair`).
* `S2019CorrectedRootStackDatum K l`: S1997's root stackification with the weak
  `isStack` field replaced by `S2019FullIsStack`; comparison and origin
  faithfulness unchanged. `.toRecorded` / `.ofRecorded` are the two directions.
* `S2019RebasedRootStackRoute l`: corrected root stack datum over S1726K plus
  corrected finite-etale data of all covers.

## What is proved (all unconditional, from the existing tree)

* `S2019IsoCommaDescent_iff_essSurj`: for a prestack, the corrected full descent
  datum is equivalent to essential surjectivity of the descent functor (recorded
  effective descent).  The uniqueness half comes from full faithfulness.
* `S2019FullIsStack_iff_IsStack`: corrected full stackhood is equivalent to
  Mathlib's `IsStack`.
* `S2019RootIsStack_iff_fullDescentAll`: root `IsStack` is exactly the
  corrected full descent datum at every covering sieve.
* `S2019RootFullDescentAll_iff_effDescent`: the corrected full descent datum is
  exactly `S1997RootEffectiveDescent K l`.  Central audit finding: the S2015 repair
  changes nothing at the effective-descent level, so the Kummer non-effectivity is
  intrinsic and not an artefact of a weak formulation.
* `S2019CorrectedFiniteEtaleAll_uniq` and
  `S2019UniqFirstMissing_of_identityPresentations`: the corrected cover data
  implies `S2001UniqFirstMissing`.
* `S2019CorrectedFull_iff_missingHalf`: for a fixed weak witness, the corrected
  full property is exactly the missing half `S1827EssSurjOf`.
* `S2019_noSchemaFromWitness` / `S2019_counterexample_identity_not_corrected` /
  `S2019_recorded_full_refuted`: the recorded weak witnesses do not produce the
  corrected presentations (S2015/S2010 re-exported).
* `S2019CorrectedRootStackMissing_iff`: the corrected root stack datum is
  inhabited iff S1997's recorded root stackification is (exact rebasing).
* `S2019CorrectedRootStackMissing_implies_S1994`: a corrected root stack datum
  over `A.K` yields `S1994StackyOrbicurveMissing l A`;
  `S2019CorrectedRootStack_witness_aut` / `..._not_discreteFiber` transport the
  order-l origin automorphism and non-discreteness.
* `S2019RebasedRootStackRoute_iff`: the route is exactly the recorded root
  stackification together with S2015's corrected finite-etale data;
  `S2019RebasedRootStackRoute_uniq` gives `S2001UniqFirstMissing`.

## Exact first missing (not proved, as instructed)

`S2019FirstMissing K l` = corrected full (actual iso-comma) descent datum of
`S1997RootPrestack K l` at every covering sieve.  It is equivalent to
`S1997RootEffectiveDescent K l` and to `IsStack` for the root prestack
(`S2019FirstMissing_iff_effDescent`, `S2019FirstMissing_iff_IsStack`).
Per the S2002/S2010 expectation it is expected to fail for Kummer covers; no proof is
attempted and no inhabitant is asserted.

## Honest boundary

No `sorry`, no new axiom, no `Shrink`/`ULift`/`PUnit`, no fabricated stack,
equivalence or 2-cell.  The stack half of the rebasing is proved equivalent to the
recorded interface; the cover half is exactly S2015's corrected data and its
strictness is the refuted in-place upgrade (S2010).  Independence of the two halves
is not claimed as a theorem.
