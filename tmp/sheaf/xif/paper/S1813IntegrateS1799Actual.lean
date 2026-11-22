import tmp.sheaf.xif.paper.S1799AffineFiniteEtaleEquivActual
import tmp.sheaf.xif.paper.S1779CorrectFiniteEtaleTargetActual

/-!
# S1813: integrating the actual S1799 affine equivalence into the S1779 route

## The new input

S1799 proves, for an arbitrary commutative ring `R`,

    affineFiniteEtaleEquivalence R :
      (CommAlgCat.FiniteEtale R)^op ≌ FiniteEtaleCover (Spec R).

At the S1779 coordinate ring

    R' = S1779R = S1726CoordinateRing
       = F'[x,y]/(y^2 - x^3 - (61/64)x^2 + (125/64)x),

this is an actual equivalence

    S1779AlgR ≌ FiniteEtaleCover (Spec R'),

where `S1779AlgR` is definitionally `(CommAlgCat.FiniteEtale.{0} R')^op`.
Thus the *algebra-side* half of the S1779 first-missing datum is now
unconditional.

## The one remaining bridge

The S1779 route still needs a genuine `Category.{0,1}` on the actual cover
type `S1728Cover = Iut.OrbicurveFiniteEtaleCover S1726Orbicurve`, whose hom
types are equivalent to the actual cover maps `S1728CoverMap A B`, together
with an equivalence

    S1728Cover ≌ FiniteEtaleCover (Spec R').

This file packages exactly that datum as `S1813ActualCoverFiniteEtaleBridge`.
It is **not** constructed here: the actual covers are etale stacks over the
orbicurve, while `FiniteEtaleCover (Spec R')` is the ordinary category of
schemes finite etale over the affine base.  The comparison is S1743's
`S1743SliceFunctorMissing` (equivalently S1733's
`S1733CoverSliceEquivalence`) composed with the affine
`FiniteEtaleCover (Spec R') ≌ S1733Slice` comparison.  The tree does not
contain either comparison, so no inhabitant is asserted.

## What this file proves

* `S1813AlgCoverEquivalence`: S1799 instantiated at `R'`, as a named actual
  equivalence, with its object map recorded.
* `S1813ActualCoverFiniteEtaleBridge`: the exact remaining bridge datum.
* `S1813AffineRoute_of_bridge`: the bridge, together with S1799, constructs
  the S1779 affine route `S1779AffineRoute` (category, hom equivalence and
  equivalence to `(FiniteEtale R')^op`).
* `S1813Bridge_of_route`: conversely the S1779 route constructs the bridge
  by composing with S1799.  Hence, by `S1813Bridge_nonempty_iff_firstMissing`,
  the exact first missing input of S1779 is *exactly* this bridge: S1799 has
  removed the algebra-side equivalence from the list of missing inputs.
* `S1813CoverPreGaloisCategory` and `S1813CoverGaloisData`: the
  S1793-shaped Galois data (pre-Galois category, fibre functor and its fibre
  functor structure) transported across the actual S1799 equivalence to the
  honest finite-etale cover category of `Spec R'`.  This is genuine transport
  by S1753's kernel-checked `S1753PreGaloisCategory` and
  `S1753FiberFunctorTransport`, not a placeholder.
* `S1813TargetFields_of_bridge` and `S1813TargetFields_of_bridge'`: the four
  target fields `S1779TargetFields` from the bridge and the exact remaining
  algebra-side fields G2/G3/fibre (or a separately supplied
  `PreGaloisCategory` and fibre functor).
* `S1813BridgeMissing`: the exact first missing proposition, proved equivalent
  to S1779's `S1779FirstMissing` and to `Nonempty S1779AffineRoute`.

No `sorry`, `admit`, new axiom, `Shrink`, `ULift` or `PUnit` is used.  The
axiom footprint of every declaration is checked at the end and must be only
`propext`, `Classical.choice` and `Quot.sound`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.defProp false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1813IntegrateS1799Actual

open CategoryTheory
open LeanFormal.IUT.XiFPaper.S1799AffineFiniteEtaleEquivActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1753OrbicurveEtalePiAssemblyActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

/-! ## 1. S1799 at the S1779 coordinate ring -/

/-- The coordinate ring `R'` of S1779, definitionally S1726's coordinate ring. -/
abbrev S1813R : Type := S1779R

/-- S1799's affine finite-etale comparison, instantiated at `R'`.  This is an
actual equivalence, kernel checked in S1799 for every commutative ring. -/
noncomputable abbrev S1813AlgCoverEquivalence :
    S1779AlgR ≌ FiniteEtaleCover (specBase S1813R) :=
  affineFiniteEtaleEquivalence S1813R

/-- The functor of the S1799 equivalence is literally S1799's `algToCover`. -/
@[simp] theorem S1813AlgCoverEquivalence_functor :
    S1813AlgCoverEquivalence.functor = algToCover S1813R := rfl

/-- On objects the S1799 equivalence is `A ↦ Spec A ⟶ Spec R'`. -/
@[simp] theorem S1813AlgCoverEquivalence_obj (A : S1779AlgR) :
    S1813AlgCoverEquivalence.functor.obj A =
      finiteEtaleAlgebraCover S1813R A.unop := rfl

/-! ## 2. The exact remaining bridge -/

/-- **The exact remaining input of the S1779 route.**  A genuine
`Category.{0,1}` on the actual S1728 cover type, whose hom types are the
actual cover maps, together with an equivalence to the honest category
`FiniteEtaleCover (Spec R')`.

This is the composition of the still-missing actual-cover/affine-slice
comparison with the affine `FiniteEtaleCover (Spec R') ≌ S1733Slice`
comparison.  No inhabitant is asserted; see `S1813BridgeMissing` below. -/
structure S1813ActualCoverFiniteEtaleBridge where
  /-- The `Category.{0,1}` structure on the actual cover type. -/
  coverCategory : Category.{0, 1} S1728Cover
  /-- Its homs are the actual cover maps. -/
  coverHomEquiv : ∀ A B,
    @Quiver.Hom _ coverCategory.toQuiver A B ≃ S1728CoverMap A B
  /-- The equivalence to the honest finite-etale covers of `Spec R'`. -/
  equivalence : @CategoryTheory.Equivalence S1728Cover
    (FiniteEtaleCover (specBase S1813R)) coverCategory
    (inferInstance : Category.{0, 1} (FiniteEtaleCover (specBase S1813R)))

/-! ## 3. The bridge together with S1799 is exactly the S1779 affine route -/

/-- The bridge and S1799 construct the S1779 affine route.  The equivalence
to `S1779AlgR = (FiniteEtale R')^op` is the bridge followed by the inverse of
the actual S1799 equivalence. -/
noncomputable def S1813AffineRoute_of_bridge
    (B : S1813ActualCoverFiniteEtaleBridge) : S1779AffineRoute where
  coverCategory := B.coverCategory
  coverHomEquiv := B.coverHomEquiv
  equivalence := by
    letI : Category.{0, 1} S1728Cover := B.coverCategory
    exact B.equivalence.trans S1813AlgCoverEquivalence.symm

/-- Conversely, the S1779 affine route and S1799 construct the bridge.  The
equivalence to `FiniteEtaleCover (Spec R')` is the route followed by the
actual S1799 equivalence. -/
noncomputable def S1813Bridge_of_route
    (R : S1779AffineRoute) : S1813ActualCoverFiniteEtaleBridge where
  coverCategory := R.coverCategory
  coverHomEquiv := R.coverHomEquiv
  equivalence := by
    letI : Category.{0, 1} S1728Cover := R.coverCategory
    exact R.equivalence.trans S1813AlgCoverEquivalence

/-- The bridge is nonempty iff the S1779 affine route is nonempty. -/
theorem S1813Bridge_nonempty_iff_route :
    Nonempty S1813ActualCoverFiniteEtaleBridge ↔ Nonempty S1779AffineRoute :=
  ⟨fun h => ⟨S1813AffineRoute_of_bridge h.some⟩,
    fun h => ⟨S1813Bridge_of_route h.some⟩⟩

/-- **The exact integration statement.**  After S1799, the S1779 first
missing input is exactly the actual-cover/`FiniteEtaleCover (Spec R')` bridge.
No algebra-side equivalence remains missing. -/
theorem S1813Bridge_nonempty_iff_firstMissing :
    Nonempty S1813ActualCoverFiniteEtaleBridge ↔ S1779FirstMissing :=
  S1813Bridge_nonempty_iff_route.trans S1779FirstMissing_iff_route.symm

/-- The condition that the remaining bridge exists.  This is the exact first
missing input of the S1779 route at the current version. -/
def S1813BridgeMissing : Prop :=
  Nonempty S1813ActualCoverFiniteEtaleBridge

/-- `S1813BridgeMissing` is exactly S1779's `S1779FirstMissing`. -/
theorem S1813BridgeMissing_iff_firstMissing :
    S1813BridgeMissing ↔ S1779FirstMissing :=
  S1813Bridge_nonempty_iff_firstMissing

/-- `S1813BridgeMissing` is exactly the existence of the S1779 affine route. -/
theorem S1813BridgeMissing_iff_route :
    S1813BridgeMissing ↔ Nonempty S1779AffineRoute :=
  S1813Bridge_nonempty_iff_route

/-- The bridge alone supplies the target's `coverCategory` field. -/
theorem S1813Category01_of_bridge (B : S1813ActualCoverFiniteEtaleBridge) :
    Nonempty (Category.{0, 1} S1728Cover) :=
  ⟨B.coverCategory⟩

/-! ## 4. The S1793-shaped Galois data, transported across S1799 -/

/-- The honest finite-etale cover category of `Spec R'` with its actual
`Category.{0,1}` structure. -/
abbrev S1813CoverCat : Type 1 :=
  FiniteEtaleCover (specBase S1813R)

/-- The pre-Galois structure on `FiniteEtaleCover (Spec R')` obtained from a
pre-Galois structure on `S1779AlgR` by the actual S1799 equivalence.  This is
S1753's genuine transport `S1753PreGaloisCategory`. -/
@[reducible]
noncomputable def S1813CoverPreGaloisCategory
    (hPre : PreGaloisCategory S1779AlgR) :
    PreGaloisCategory S1813CoverCat := by
  letI : PreGaloisCategory S1779AlgR := hPre
  exact S1753PreGaloisCategory S1813AlgCoverEquivalence.symm

/-- The S1793-shaped Galois data (a pre-Galois category and a fibre functor
with its fibre-functor structure) on the honest finite-etale covers of
`Spec R'`. -/
structure S1813CoverGaloisData where
  /-- The pre-Galois category. -/
  preGalois : PreGaloisCategory S1813CoverCat
  /-- The fibre functor. -/
  fiber : S1813CoverCat ⥤ FintypeCat.{0}
  /-- The fibre-functor structure. -/
  fiberFunctor : @PreGaloisCategory.FiberFunctor S1813CoverCat
    (inferInstance : Category.{0, 1} S1813CoverCat) preGalois fiber

/-- Transport the S1779 algebra-side Galois data to the honest
`FiniteEtaleCover (Spec R')` side across the actual S1799 equivalence.  Both
the pre-Galois structure and the fibre functor are transported by S1753's
kernel-checked constructions; nothing is postulated. -/
noncomputable def S1813CoverGaloisData_of_alg
    (D : S1779AlgGaloisData) : S1813CoverGaloisData where
  preGalois := S1813CoverPreGaloisCategory D.preGalois
  fiber := S1813AlgCoverEquivalence.symm.functor ⋙ D.fiber
  fiberFunctor := by
    letI : PreGaloisCategory S1779AlgR := D.preGalois
    letI : PreGaloisCategory.FiberFunctor D.fiber := D.fiberFunctor
    exact S1753FiberFunctorTransport S1813AlgCoverEquivalence.symm D.fiber

/-- The S1793-shaped Galois data on `FiniteEtaleCover (Spec R')` from the
exact remaining algebra-side fields G2/G3 and the geometric fibre functor. -/
noncomputable def S1813CoverGaloisData_of_missing
    (hQuot : S1779QuotientsMissing) (hMono : S1779MonoMissing)
    (hFiber : S1779FiberFunctorMissing (S1779PreGaloisCategory hQuot hMono)) :
    S1813CoverGaloisData :=
  S1813CoverGaloisData_of_alg
    (S1779AlgGaloisData_of_missing hQuot hMono hFiber)


/-- The Galois-category structure assembled from the S1793-shaped data.  This
is the same `GaloisCategory.mk` assembly used by `S1779TargetFields_of_route`,
now on the honest `FiniteEtaleCover (Spec R')` side. -/
noncomputable def S1813CoverGaloisData.galoisCategory
    (D : S1813CoverGaloisData) : GaloisCategory S1813CoverCat := by
  letI : PreGaloisCategory S1813CoverCat := D.preGalois
  letI : PreGaloisCategory.FiberFunctor D.fiber := D.fiberFunctor
  exact GaloisCategory.mk ⟨D.fiber, ⟨D.fiberFunctor⟩⟩

/-! ## 5. The four target fields -/

/-- From the bridge and the exact algebra-side Galois data, the four target
fields are obtained by the genuine S1753 transport used in
`S1779TargetFields_of_route`. -/
theorem S1813TargetFields_of_bridge_and_galoisData
    (B : S1813ActualCoverFiniteEtaleBridge) (D : S1779AlgGaloisData) :
    Nonempty S1779TargetFields :=
  ⟨S1779TargetFields_of_route (S1813AffineRoute_of_bridge B) D⟩

/-- From the bridge, G2/G3 over `R'` and the geometric fibre-functor
structure, the four target fields are obtained. -/
theorem S1813TargetFields_of_bridge
    (B : S1813ActualCoverFiniteEtaleBridge)
    (hQuot : S1779QuotientsMissing) (hMono : S1779MonoMissing)
    (hFiber : S1779FiberFunctorMissing (S1779PreGaloisCategory hQuot hMono)) :
    Nonempty S1779TargetFields :=
  S1813TargetFields_of_bridge_and_galoisData B
    (S1779AlgGaloisData_of_missing hQuot hMono hFiber)

/-- The same target-field assembly with a separately supplied
`PreGaloisCategory S1779AlgR` and fibre functor. -/
theorem S1813TargetFields_of_bridge'
    (B : S1813ActualCoverFiniteEtaleBridge)
    (hPre : PreGaloisCategory S1779AlgR)
    (hFiber : S1779FiberFunctorMissing hPre) :
    Nonempty S1779TargetFields := by
  exact ⟨S1779TargetFields_of_route (S1813AffineRoute_of_bridge B)
    { preGalois := hPre
      fiber := S1779GeometricFiber
      fiberFunctor := hFiber }⟩

/-! ## 6. The S1799 output and the affine finite-etale slice

S1777's target is an equivalence `S1779AlgR ≌ S1733Slice`.  By S1799 this is
*equivalent* to an equivalence `FiniteEtaleCover (Spec R') ≌ S1733Slice`: the
algebra side can be replaced by the honest cover side at no cost.  We record
the two directions and the resulting equivalence of existence statements.

This does not construct the still-missing actual-cover/slice comparison: it
only removes the algebra side from the S1777 target using the actual S1799
equivalence. -/

/-- S1799 converts a S1777 algebra/slice equivalence into a
finite-etale-cover/slice equivalence. -/
noncomputable def S1813CoverSliceEquivalence_of_algSlice
    (e : S1779AlgR ≌ S1733Slice) :
    FiniteEtaleCover (specBase S1813R) ≌ S1733Slice :=
  S1813AlgCoverEquivalence.symm.trans e

/-- Conversely, S1799 converts a finite-etale-cover/slice equivalence into a
S1777 algebra/slice equivalence. -/
noncomputable def S1813AlgSliceEquivalence_of_coverSlice
    (e : FiniteEtaleCover (specBase S1813R) ≌ S1733Slice) :
    S1779AlgR ≌ S1733Slice :=
  S1813AlgCoverEquivalence.trans e

/-- The S1777 affine-slice equivalence target and the honest
finite-etale-cover/slice equivalence have the same existence content after
S1799. -/
theorem S1813AffineSliceEquivalence_nonempty_iff_coverSlice :
    S1779AffineSliceEquivalenceMissing ↔
      Nonempty (FiniteEtaleCover (specBase S1813R) ≌ S1779Slice) := by
  change Nonempty (S1779AlgR ≌ S1779Slice) ↔
    Nonempty (FiniteEtaleCover (specBase S1813R) ≌ S1779Slice)
  exact ⟨fun h => ⟨S1813CoverSliceEquivalence_of_algSlice h.some⟩,
    fun h => ⟨S1813AlgSliceEquivalence_of_coverSlice h.some⟩⟩

/-- The actual-cover/slice version of the bridge: a `Category.{0,1}` on the
actual cover type with actual cover maps as homs, and an equivalence to the
S1733 affine finite-etale slice.  This is the S1743/S1733 shape with the
`Category.{0,1}`/raw-hom content of S1779 made explicit. -/
structure S1813ActualCoverSliceBridge where
  /-- The small category structure on the actual cover type. -/
  coverCategory : Category.{0, 1} S1728Cover
  /-- Its homs are the actual cover maps. -/
  coverHomEquiv : ∀ A B,
    @Quiver.Hom _ coverCategory.toQuiver A B ≃ S1728CoverMap A B
  /-- The equivalence to the affine finite-etale slice. -/
  equivalence : @CategoryTheory.Equivalence S1728Cover S1733Slice
    coverCategory (inferInstance : Category.{0, 1} S1733Slice)

/-- An actual-cover/slice bridge plus a finite-etale-cover/slice equivalence
gives the actual-cover/`FiniteEtaleCover` bridge. -/
theorem S1813Bridge_of_sliceBridge
    (h : S1813ActualCoverSliceBridge)
    (e : FiniteEtaleCover (specBase S1813R) ≌ S1733Slice) :
    Nonempty S1813ActualCoverFiniteEtaleBridge := by
  letI : Category.{0, 1} S1728Cover := h.coverCategory
  exact ⟨{ coverCategory := h.coverCategory
           coverHomEquiv := h.coverHomEquiv
           equivalence := h.equivalence.trans e.symm }⟩

/-- In particular, S1777's algebra/slice equivalence and an
actual-cover/slice bridge suffice for the remaining S1779 input. -/
theorem S1813Bridge_of_algSlice_and_coverSlice
    (e : S1779AlgR ≌ S1733Slice)
    (h : S1813ActualCoverSliceBridge) :
    Nonempty S1813ActualCoverFiniteEtaleBridge :=
  S1813Bridge_of_sliceBridge h (S1813CoverSliceEquivalence_of_algSlice e)

/-! ## 7. Checks and axiom audit -/

#check S1813R
#check S1813AlgCoverEquivalence
#check S1813AlgCoverEquivalence_functor
#check S1813AlgCoverEquivalence_obj
#check S1813ActualCoverFiniteEtaleBridge
#check S1813AffineRoute_of_bridge
#check S1813Bridge_of_route
#check S1813Bridge_nonempty_iff_route
#check S1813Bridge_nonempty_iff_firstMissing
#check S1813BridgeMissing
#check S1813BridgeMissing_iff_firstMissing
#check S1813BridgeMissing_iff_route
#check S1813Category01_of_bridge
#check S1813CoverCat
#check S1813CoverPreGaloisCategory
#check S1813CoverGaloisData
#check S1813CoverGaloisData_of_alg
#check S1813CoverGaloisData_of_missing
#check S1813CoverGaloisData.galoisCategory
#check S1813TargetFields_of_bridge_and_galoisData
#check S1813TargetFields_of_bridge
#check S1813TargetFields_of_bridge'
#check S1813CoverSliceEquivalence_of_algSlice
#check S1813AlgSliceEquivalence_of_coverSlice
#check S1813AffineSliceEquivalence_nonempty_iff_coverSlice
#check S1813ActualCoverSliceBridge
#check S1813Bridge_of_sliceBridge
#check S1813Bridge_of_algSlice_and_coverSlice


#print axioms S1813AlgCoverEquivalence
#print axioms S1813AlgCoverEquivalence_obj
#print axioms S1813AffineRoute_of_bridge
#print axioms S1813Bridge_of_route
#print axioms S1813Bridge_nonempty_iff_route
#print axioms S1813Bridge_nonempty_iff_firstMissing
#print axioms S1813BridgeMissing_iff_firstMissing
#print axioms S1813Category01_of_bridge
#print axioms S1813CoverPreGaloisCategory
#print axioms S1813CoverGaloisData_of_alg
#print axioms S1813CoverGaloisData_of_missing
#print axioms S1813CoverGaloisData.galoisCategory
#print axioms S1813TargetFields_of_bridge_and_galoisData
#print axioms S1813TargetFields_of_bridge
#print axioms S1813TargetFields_of_bridge'
#print axioms S1813CoverSliceEquivalence_of_algSlice
#print axioms S1813AlgSliceEquivalence_of_coverSlice
#print axioms S1813AffineSliceEquivalence_nonempty_iff_coverSlice
#print axioms S1813Bridge_of_sliceBridge
#print axioms S1813Bridge_of_algSlice_and_coverSlice

