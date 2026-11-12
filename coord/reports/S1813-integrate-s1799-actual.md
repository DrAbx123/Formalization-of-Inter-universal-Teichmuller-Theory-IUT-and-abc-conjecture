# S1813: integrating the actual S1799 affine equivalence into the S1779 route

Status: proof file compiled; integration complete at the exact first missing.
Consumer: S1779CorrectFiniteEtaleTargetActual (and the S1793-shaped Galois
data / S1779TargetFields route), which previously had to assume the removed
S1777 affine equivalence.

## 1. The new actual input

S1799AffineFiniteEtaleEquivActual proves, for every commutative ring `R`,

    affineFiniteEtaleEquivalence R :
      (CommAlgCat.FiniteEtale R)^op ≌ FiniteEtaleCover (Spec R).

At the S1779 coordinate ring

    R' = S1779R = S1726CoordinateRing
       = F'[x,y]/(y^2 - x^3 - (61/64)x^2 + (125/64)x),

this gives the actual equivalence

    S1813AlgCoverEquivalence :
      S1779AlgR ≌ FiniteEtaleCover (Spec R'),

where `S1779AlgR` is definitionally `(CommAlgCat.FiniteEtale.{0} R')^op`.
The functor and object map are recorded as literally S1799's `algToCover` and
`finiteEtaleAlgebraCover`.

## 2. What the file constructs

`tmp/sheaf/xif/paper/S1813IntegrateS1799Actual.lean` defines:

* `S1813ActualCoverFiniteEtaleBridge`: a `Category.{0,1}` on the actual
  S1728 cover type, whose homs are equivalent to the actual cover maps
  `S1728CoverMap A B`, together with an equivalence
  `S1728Cover ≌ FiniteEtaleCover (Spec R')`.
* `S1813AffineRoute_of_bridge`: this bridge plus S1799 gives
  `S1779AffineRoute`.
* `S1813Bridge_of_route`: conversely, `S1779AffineRoute` plus S1799 gives the
  bridge.  Hence
  `S1813Bridge_nonempty_iff_firstMissing`:
  `Nonempty S1813ActualCoverFiniteEtaleBridge ↔ S1779FirstMissing`.
* `S1813BridgeMissing`: the exact missing proposition, with
  `S1813BridgeMissing ↔ S1779FirstMissing` and
  `S1813BridgeMissing ↔ Nonempty S1779AffineRoute`.
* `S1813CoverPreGaloisCategory`, `S1813CoverGaloisData_of_alg` and
  `S1813CoverGaloisData.galoisCategory`: the S1793-shaped Galois data
  (pre-Galois category, fibre functor, fibre-functor structure, assembled
  Galois category) transported across the actual S1799 equivalence by S1753's
  kernel-checked `S1753PreGaloisCategory` / `S1753FiberFunctorTransport`.
* `S1813CoverGaloisData_of_missing`: the same from S1779's exact remaining
  algebra-side fields G2/G3 and the geometric fibre functor.
* `S1813TargetFields_of_bridge_and_galoisData`,
  `S1813TargetFields_of_bridge`, `S1813TargetFields_of_bridge'`: the four
  target fields `S1779TargetFields`.
* `S1813CoverSliceEquivalence_of_algSlice`,
  `S1813AlgSliceEquivalence_of_coverSlice` and
  `S1813AffineSliceEquivalence_nonempty_iff_coverSlice`: S1799 identifies the
  S1777 algebra/slice equivalence target with the honest
  `FiniteEtaleCover (Spec R') ≌ S1733Slice` target.
* `S1813ActualCoverSliceBridge` and
  `S1813Bridge_of_algSlice_and_coverSlice`: the decomposition of the remaining
  bridge into the actual-cover/slice comparison and the S1777 algebra/slice
  equivalence.

## 3. The exact first missing

The first missing input of the S1779 route is exactly

    S1813BridgeMissing
      = Nonempty (actual cover category ≌ FiniteEtaleCover (Spec R')).

S1799 has removed the algebra side from the missing list: the bridge is now
equivalent to the old `S1779FirstMissing`.  It is *not* constructed, because
the actual covers are etale stacks over the orbicurve, while
`FiniteEtaleCover (Spec R')` is the ordinary category of schemes finite etale
over the affine base.  The comparison decomposes as

    (actual cover ↔ affine finite-etale slice)
      + (affine slice ≌ FiniteEtaleCover (Spec R')),

where the first is S1743/S1733's remaining cover/slice comparison
(`S1743SliceFunctorMissing` / `S1733CoverSliceEquivalence`, ultimately
S1784's `S1784LiftEssSurj` / S1758's `S1758LiftConeIso`) and the second is
what S1799 + S1777's algebra/slice equivalence supplies.

After the bridge, the remaining inputs for `S1779TargetFields` are exactly
S1779's algebra-side fields:

* `S1779QuotientsMissing` (G2 over R'),
* `S1779MonoMissing` (G3 over R'),
* `S1779FiberFunctorMissing` for the geometric fibre at (0,0).

No fake category, equivalence, fibre functor or target field is introduced.

## 4. Verification

Source: tmp/sheaf/xif/paper/S1813IntegrateS1799Actual.lean
Source size: 18410 bytes
Source SHA256: 045C4D860908FF5101FB78CE73151BFB899812B62176FB54289AB5A823695CF6
Compile: lean -j1 -o ... (direct, LEAN_PATH from lake env), EXIT=0,
  no error lines, no sorryAx lines, no warnings
Olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1813IntegrateS1799Actual.olean
Olean size: 175840 bytes
Olean SHA256: 135553287968506BFBDF1E4752C2BF0CAD45796A05A2FEA6A9C2C01EFB3EBFBD
Axioms: propext, Classical.choice, Quot.sound only for every #print axioms
  declaration in the file; zero sorryAx.

## 5. Honest boundary

* S1813AlgCoverEquivalence is actual (S1799).
* The bridge is an explicit missing structure, not an axiom or a fake.
* The conditional constructions are real proofs from the stated inputs.
* `S1779TargetFields` is not asserted unconditionally: it needs the bridge and
  the S1779 G2/G3/fibre fields.
