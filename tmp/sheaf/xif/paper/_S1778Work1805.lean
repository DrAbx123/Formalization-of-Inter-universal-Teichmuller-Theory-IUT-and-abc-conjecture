/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1778
-/
import tmp.sheaf.xif.paper.S1779CorrectFiniteEtaleTargetActual
import Mathlib.CategoryTheory.InducedCategory
import Mathlib.CategoryTheory.EssentiallySmall

/-!
# S1778: `Category.{0,1}` on the actual cover type via finite etale `R'`-algebras

The actual cover type is `S1778Cover = Iut.OrbicurveFiniteEtaleCover S1726Orbicurve`
(a `Type 1`).  Its finite etale covers correspond to finite etale algebras over
the coordinate ring

  `R' = S1726CoordinateRing = F'[x,y]/(y^2 - x^3 - (61/64)x^2 + (125/64)x)`

of `E' - O`; the corrected algebra-side target is

  `S1778AlgR = (CommAlgCat.FiniteEtale.{0} R')ᵒᵖ`   (`Category.{0,1}`).

Given the affine equivalence

  `e : S1778Cover ≌ S1778AlgR`

(which S1777 is expected to supply), this file constructs:

1. `S1778CoverCategoryOfEquivalence e : Category.{0,1} S1778Cover`, the
   `InducedCategory` structure whose homs are
   `e.functor.obj A ⟶ e.functor.obj B`.  This is a genuine category on the
   actual cover type, not a `Shrink`/`ULift`/`PUnit` fake.
2. Equivalences `S1778CoverCategoryEquivalence e` (to `S1778AlgR`) and
   `S1778CoverCategoryEquivalenceActual e` (to the S1728 `Category.{1,1}`).
3. `S1778PreGaloisCategory`, `S1778FiberFunctorTransport`,
   `S1778GaloisCategory`, reusing the kernel-checked generic transport of
   S1753 (no field is reproved or assumed beyond the algebra-side input).
4. `EssentiallySmall.{0}` transport from the algebra side and from the
   actual S1728 category.
5. The four target fields (`S1753TargetFields`, literally the fields of
   `Iut.OrbicurveEtaleFundamentalGroup`), including the concrete instance from
   S1779's exact missing algebra-side fields.

## Honest boundary

No S1777 module exists in this checkout at the time of writing, so `e` is an
explicit hypothesis.  The algebra-side Galois structures are hypotheses (or
S1779's exact missing propositions), and `EssentiallySmall` of `S1778AlgR` is
transported when supplied.  No `sorry`, `axiom` or fake instance; axiom audit
at the end.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1778Category01ViaAlgebrasActual

open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper

/-! ## 1. The actual cover type and the corrected algebra category -/

/-- The actual cover type of the S1726 D6 orbicurve. -/
abbrev S1778Cover : Type 1 := S1728Cover

/-- The corrected algebra side: finite etale algebras over `R'`, opposite. -/
abbrev S1778AlgR : Type 1 :=
  LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual.S1779AlgR

/-- The `Category.{0,1}` structure on `S1778AlgR` (definitionally S1779's). -/
instance S1778AlgR_category : Category.{0, 1} S1778AlgR :=
  LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual.S1779AlgR_category

/-! ## 2. The transported category and its equivalences -/

/-- The `Category.{0,1}` structure on the actual cover type induced by the
object map of the affine equivalence. -/
@[reducible]
noncomputable def S1778CoverCategoryOfEquivalence
    (e : S1778Cover ≌ S1778AlgR) : Category.{0, 1} S1778Cover :=
  inferInstanceAs
    (Category.{0, 1}
      (InducedCategory S1778AlgR (fun X : S1778Cover => e.functor.obj X)))

/-- The induced functor from the transported category to the algebra category
is an equivalence (full/faithful by construction; essential surjectivity from
the inverse functor of `e`). -/
noncomputable instance S1778InducedFunctorIsEquivalence
    (e : S1778Cover ≌ S1778AlgR) :
    (inducedFunctor (fun X : S1778Cover => e.functor.obj X)).IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj :=
    ⟨fun Y => ⟨e.inverse.obj Y, ⟨e.counitIso.app Y⟩⟩⟩

/-- The transported category is equivalent to the corrected algebra target. -/
noncomputable def S1778CoverCategoryEquivalence
    (e : S1778Cover ≌ S1778AlgR) :
    @CategoryTheory.Equivalence S1778Cover S1778AlgR
      (S1778CoverCategoryOfEquivalence e) S1778AlgR_category :=
  (inducedFunctor (fun X : S1778Cover => e.functor.obj X)).asEquivalence

/-- The transported category is equivalent to the actual S1728 cover category
(at its genuine `Category.{1,1}` structure). -/
noncomputable def S1778CoverCategoryEquivalenceActual
    (e : S1778Cover ≌ S1778AlgR) :
    @CategoryTheory.Equivalence S1778Cover S1778Cover
      (S1778CoverCategoryOfEquivalence e) S1728ActualCategory11 := by
  letI : Category.{0, 1} S1778Cover := S1778CoverCategoryOfEquivalence e
  exact (S1778CoverCategoryEquivalence e).trans e.symm

/-! ## 3. Transport of the Galois structures -/

/-- The transported `PreGaloisCategory` on the actual cover type. -/
theorem S1778PreGaloisCategory
    (e : S1778Cover ≌ S1778AlgR)
    (P : @PreGaloisCategory S1778AlgR S1778AlgR_category) :
    @PreGaloisCategory S1778Cover (S1778CoverCategoryOfEquivalence e) := by
  letI : Category.{0, 1} S1778Cover := S1778CoverCategoryOfEquivalence e
  letI : PreGaloisCategory S1778AlgR := P
  exact LeanFormal.IUT.XiFPaper.S1753OrbicurveEtalePiAssemblyActual.S1753PreGaloisCategory
    (S1778CoverCategoryEquivalence e)

/-- The transported fiber functor structure. -/
theorem S1778FiberFunctorTransport
    (e : S1778Cover ≌ S1778AlgR)
    (P : @PreGaloisCategory S1778AlgR S1778AlgR_category)
    (F : S1778AlgR ⥤ FintypeCat.{0})
    (hF : @PreGaloisCategory.FiberFunctor S1778AlgR S1778AlgR_category P F) :
    @PreGaloisCategory.FiberFunctor S1778Cover
      (S1778CoverCategoryOfEquivalence e)
      (S1778PreGaloisCategory e P)
      (by
        letI : Category.{0, 1} S1778Cover := S1778CoverCategoryOfEquivalence e
        exact (S1778CoverCategoryEquivalence e).functor ⋙ F) := by
  letI : Category.{0, 1} S1778Cover := S1778CoverCategoryOfEquivalence e
  letI : PreGaloisCategory S1778AlgR := P
  letI : PreGaloisCategory.FiberFunctor F := hF
  exact LeanFormal.IUT.XiFPaper.S1753OrbicurveEtalePiAssemblyActual.S1753FiberFunctorTransport
    (S1778CoverCategoryEquivalence e) F

/-- The transported `GaloisCategory` on the actual cover type. -/
theorem S1778GaloisCategory
    (e : S1778Cover ≌ S1778AlgR)
    (P : @PreGaloisCategory S1778AlgR S1778AlgR_category)
    (F : S1778AlgR ⥤ FintypeCat.{0})
    (hF : @PreGaloisCategory.FiberFunctor S1778AlgR S1778AlgR_category P F) :
    @GaloisCategory S1778Cover (S1778CoverCategoryOfEquivalence e) := by
  letI : Category.{0, 1} S1778Cover := S1778CoverCategoryOfEquivalence e
  letI : PreGaloisCategory S1778AlgR := P
  letI : PreGaloisCategory.FiberFunctor F := hF
  exact LeanFormal.IUT.XiFPaper.S1753OrbicurveEtalePiAssemblyActual.S1753GaloisCategoryOfFiber
    (S1778CoverCategoryEquivalence e) F

/-! ## 4. Transport of `EssentiallySmall` -/

/-- `EssentiallySmall` of the transported category, from the algebra side. -/
theorem S1778EssentiallySmallOfAlgebra
    (e : S1778Cover ≌ S1778AlgR)
    (h : @EssentiallySmall.{0} S1778AlgR S1778AlgR_category) :
    @EssentiallySmall.{0} S1778Cover (S1778CoverCategoryOfEquivalence e) := by
  letI : Category.{0, 1} S1778Cover := S1778CoverCategoryOfEquivalence e
  exact (essentiallySmall_congr (S1778CoverCategoryEquivalence e)).mpr h

/-- `EssentiallySmall` of the transported category, from the actual S1728 cover
category at its genuine `Category.{1,1}` structure. -/
theorem S1778EssentiallySmallOfActual
    (e : S1778Cover ≌ S1778AlgR)
    (h : @EssentiallySmall.{0} S1778Cover S1728ActualCategory11) :
    @EssentiallySmall.{0} S1778Cover (S1778CoverCategoryOfEquivalence e) := by
  letI : Category.{0, 1} S1778Cover := S1778CoverCategoryOfEquivalence e
  exact (essentiallySmall_congr (S1778CoverCategoryEquivalenceActual e)).mpr h

/-! ## 5. The four target fields -/

/-- The four target fields, assembled from the equivalence, an algebra-side
`PreGaloisCategory`, a fiber functor and its fiber-functor structure. -/
noncomputable def S1778TargetFields
    (e : S1778Cover ≌ S1778AlgR)
    (P : @PreGaloisCategory S1778AlgR S1778AlgR_category)
    (F : S1778AlgR ⥤ FintypeCat.{0})
    (hF : @PreGaloisCategory.FiberFunctor S1778AlgR S1778AlgR_category P F) :
    LeanFormal.IUT.XiFPaper.S1753OrbicurveEtalePiAssemblyActual.S1753TargetFields := by
  letI : Category.{0, 1} S1778Cover := S1778CoverCategoryOfEquivalence e
  letI : PreGaloisCategory S1778AlgR := P
  letI : PreGaloisCategory.FiberFunctor F := hF
  letI : GaloisCategory S1778AlgR := GaloisCategory.mk ⟨F, ⟨hF⟩⟩
  exact
    { coverCategory := S1778CoverCategoryOfEquivalence e
      galoisCategory :=
        LeanFormal.IUT.XiFPaper.S1753OrbicurveEtalePiAssemblyActual.S1753GaloisCategoryOfFiber
          (S1778CoverCategoryEquivalence e) F
      fiber := (S1778CoverCategoryEquivalence e).functor ⋙ F
      fiberFunctor :=
        LeanFormal.IUT.XiFPaper.S1753OrbicurveEtalePiAssemblyActual.S1753FiberFunctorTransport
          (S1778CoverCategoryEquivalence e) F }

/-- The concrete target fields from the equivalence and S1779's exact missing
algebra-side data. -/
noncomputable def S1778TargetFieldsOfMissing
    (e : S1778Cover ≌ S1778AlgR)
    (hQuot : LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual.S1779QuotientsMissing)
    (hMono : LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual.S1779MonoMissing)
    (hFiber : LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual.S1779FiberFunctorMissing
      (LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual.S1779PreGaloisCategory hQuot hMono)) :
    LeanFormal.IUT.XiFPaper.S1753OrbicurveEtalePiAssemblyActual.S1753TargetFields :=
  S1778TargetFields e
    (LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual.S1779PreGaloisCategory hQuot hMono)
    LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual.S1779GeometricFiber
    hFiber

/-! ## 6. Route form: an arbitrary `Category.{0,1}` on the cover type

If S1777 constructs its own `Category.{0,1}` on the actual cover type (rather
than using the S1728 quotient category), the following interface applies
verbatim: it transports PreGalois/Galois/fiber functors and `EssentiallySmall`
along the equivalence at that category. -/

/-- PreGalois transport for an arbitrary category structure on the cover type. -/
theorem S1778PreGaloisCategoryOfRoute
    (C : Category.{0, 1} S1778Cover)
    (e : @CategoryTheory.Equivalence S1778Cover S1778AlgR C S1778AlgR_category)
    (P : @PreGaloisCategory S1778AlgR S1778AlgR_category) :
    @PreGaloisCategory S1778Cover C := by
  letI : Category.{0, 1} S1778Cover := C
  letI : PreGaloisCategory S1778AlgR := P
  exact LeanFormal.IUT.XiFPaper.S1753OrbicurveEtalePiAssemblyActual.S1753PreGaloisCategory e

/-- Galois transport for an arbitrary category structure on the cover type. -/
theorem S1778GaloisCategoryOfRoute
    (C : Category.{0, 1} S1778Cover)
    (e : @CategoryTheory.Equivalence S1778Cover S1778AlgR C S1778AlgR_category)
    (P : @PreGaloisCategory S1778AlgR S1778AlgR_category)
    (F : S1778AlgR ⥤ FintypeCat.{0})
    (hF : @PreGaloisCategory.FiberFunctor S1778AlgR S1778AlgR_category P F) :
    @GaloisCategory S1778Cover C := by
  letI : Category.{0, 1} S1778Cover := C
  letI : PreGaloisCategory S1778AlgR := P
  letI : PreGaloisCategory.FiberFunctor F := hF
  exact LeanFormal.IUT.XiFPaper.S1753OrbicurveEtalePiAssemblyActual.S1753GaloisCategoryOfFiber e F

/-- `EssentiallySmall` transport for an arbitrary category structure. -/
theorem S1778EssentiallySmallOfRoute
    (C : Category.{0, 1} S1778Cover)
    (e : @CategoryTheory.Equivalence S1778Cover S1778AlgR C S1778AlgR_category)
    (h : @EssentiallySmall.{0} S1778AlgR S1778AlgR_category) :
    @EssentiallySmall.{0} S1778Cover C :=
  (essentiallySmall_congr e).mpr h

/-- The four target fields for an arbitrary category structure on the cover
type: this is the direct conditional assembly from S1777's equivalence. -/
noncomputable def S1778TargetFieldsOfRoute
    (C : Category.{0, 1} S1778Cover)
    (e : @CategoryTheory.Equivalence S1778Cover S1778AlgR C S1778AlgR_category)
    (P : @PreGaloisCategory S1778AlgR S1778AlgR_category)
    (F : S1778AlgR ⥤ FintypeCat.{0})
    (hF : @PreGaloisCategory.FiberFunctor S1778AlgR S1778AlgR_category P F) :
    LeanFormal.IUT.XiFPaper.S1753OrbicurveEtalePiAssemblyActual.S1753TargetFields := by
  letI : Category.{0, 1} S1778Cover := C
  letI : PreGaloisCategory S1778AlgR := P
  letI : PreGaloisCategory.FiberFunctor F := hF
  letI : GaloisCategory S1778AlgR := GaloisCategory.mk ⟨F, ⟨hF⟩⟩
  exact
    { coverCategory := C
      galoisCategory :=
        LeanFormal.IUT.XiFPaper.S1753OrbicurveEtalePiAssemblyActual.S1753GaloisCategoryOfFiber e F
      fiber := e.functor ⋙ F
      fiberFunctor :=
        LeanFormal.IUT.XiFPaper.S1753OrbicurveEtalePiAssemblyActual.S1753FiberFunctorTransport e F }

/-! ## 7. The exact missing input (S1777) -/

/-- The exact missing input of this route: an equivalence from the actual
S1728 cover category to the corrected target `(FiniteEtale R')ᵒᵖ`.  This is
the statement S1777 is expected to prove; the constructions above are
conditional on it. -/
def S1778AffineEquivalenceMissing : Prop :=
  Nonempty
    (@CategoryTheory.Equivalence S1778Cover S1778AlgR
      S1728ActualCategory11 S1778AlgR_category)

/-- From the exact missing equivalence, a `Category.{0,1}` on the actual cover
type exists. -/
theorem S1778CategoryOfAffineEquivalenceMissing
    (h : S1778AffineEquivalenceMissing) :
    Nonempty (Category.{0, 1} S1778Cover) := by
  rcases h with ⟨e⟩
  exact ⟨S1778CoverCategoryOfEquivalence e⟩

/-- From the exact missing equivalence and the algebra-side data, the four
target fields exist. -/
theorem S1778TargetFieldsOfAffineEquivalenceMissing
    (h : S1778AffineEquivalenceMissing)
    (P : @PreGaloisCategory S1778AlgR S1778AlgR_category)
    (F : S1778AlgR ⥤ FintypeCat.{0})
    (hF : @PreGaloisCategory.FiberFunctor S1778AlgR S1778AlgR_category P F) :
    Nonempty
      (LeanFormal.IUT.XiFPaper.S1753OrbicurveEtalePiAssemblyActual.S1753TargetFields) := by
  rcases h with ⟨e⟩
  exact ⟨S1778TargetFields e P F hF⟩

/-! ## 8. Consistency checks -/

/-- The transported category has Type-0 homs and Type-1 objects. -/
example (e : S1778Cover ≌ S1778AlgR) : Category.{0, 1} S1778Cover :=
  S1778CoverCategoryOfEquivalence e

/-- The category is definitionally the `InducedCategory` structure. -/
example (e : S1778Cover ≌ S1778AlgR) :
    S1778CoverCategoryOfEquivalence e =
      inferInstanceAs (Category.{0, 1}
        (InducedCategory S1778AlgR (fun X : S1778Cover => e.functor.obj X))) := rfl

/-- The algebra-side category of S1778 is literally S1779's corrected target. -/
example : S1778AlgR = LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual.S1779AlgR := rfl

/-! ## 9. Axiom audit -/

#print axioms S1778CoverCategoryOfEquivalence
#print axioms S1778CoverCategoryEquivalence
#print axioms S1778CoverCategoryEquivalenceActual
#print axioms S1778PreGaloisCategory
#print axioms S1778FiberFunctorTransport
#print axioms S1778GaloisCategory
#print axioms S1778EssentiallySmallOfAlgebra
#print axioms S1778EssentiallySmallOfActual
#print axioms S1778TargetFields
#print axioms S1778TargetFieldsOfMissing
#print axioms S1778PreGaloisCategoryOfRoute
#print axioms S1778GaloisCategoryOfRoute
#print axioms S1778EssentiallySmallOfRoute
#print axioms S1778TargetFieldsOfRoute
#print axioms S1778CategoryOfAffineEquivalenceMissing
#print axioms S1778TargetFieldsOfAffineEquivalenceMissing

end LeanFormal.IUT.XiFPaper.S1778Category01ViaAlgebrasActual