import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S1735Core

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut

universe u

variable {F : Type u} [Field F] {X : HyperbolicOrbicurve F}

/-- The actual geometric fiber of a cover at a scheme-valued point. -/
abbrev GeomFiber (baseScheme : SchemeOverField F)
    (point :
      Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor F baseScheme) X.stack.fiber)
    (cover : OrbicurveFiniteEtaleCover X) : Type u :=
  OrbicurveFiniteEtaleCover.GeometricFiber baseScheme point cover

/-- The actual map on geometric fibers induced by an actual cover map. -/
noncomputable def geomFiberMap (baseScheme : SchemeOverField F)
    (point :
      Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor F baseScheme) X.stack.fiber)
    {source target : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap source target) :
    GeomFiber baseScheme point source → GeomFiber baseScheme point target :=
  fun x =>
    (OrbicurveFiniteEtaleCover.geometricFiberMap
      f.map f.commutes baseScheme point).obj x

section CoverCategory

variable [Category.{u} (OrbicurveFiniteEtaleCover X)]

/-- The strict geometric-fiber data required to define an actual fiber functor
with object map GeomFiber and morphism map geomFiberMap.  The last two
fields are not derivable from the 2-category of cover maps: the available data
only gives 2-isomorphisms, not the equalities of functions. -/
structure StrictCoverData
    (baseScheme : SchemeOverField F)
    (point :
      Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor F baseScheme) X.stack.fiber) where
  /-- The actual cover map underlying a categorical arrow. -/
  coverMorphism : ∀ {A B : OrbicurveFiniteEtaleCover X},
    (A ⟶ B) → A.source.Hom B.source
  /-- The commuting 2-cell of the underlying cover map. -/
  coverMorphism_over : ∀ {A B : OrbicurveFiniteEtaleCover X}
    (f : A ⟶ B),
    Iso
      (Pseudofunctor.StrongTrans.vcomp (coverMorphism f) B.map)
      A.map
  /-- Finiteness of the actual geometric fiber. -/
  fintype : ∀ cover : OrbicurveFiniteEtaleCover X,
    Fintype (GeomFiber baseScheme point cover)
  /-- Strict identity law for the actual geometric fiber map. -/
  map_id : ∀ cover : OrbicurveFiniteEtaleCover X,
    geomFiberMap baseScheme point
        (⟨coverMorphism (𝟙 cover), coverMorphism_over (𝟙 cover)⟩ :
          OrbicurveFiniteEtaleCoverMap cover cover) = id
  /-- Strict composition law for the actual geometric fiber map. -/
  map_comp : ∀ {A B C : OrbicurveFiniteEtaleCover X}
    (f : A ⟶ B) (g : B ⟶ C),
    geomFiberMap baseScheme point
        (⟨coverMorphism (f ≫ g), coverMorphism_over (f ≫ g)⟩ :
          OrbicurveFiniteEtaleCoverMap A C) =
      geomFiberMap baseScheme point
          (⟨coverMorphism g, coverMorphism_over g⟩ :
            OrbicurveFiniteEtaleCoverMap B C) ∘
        geomFiberMap baseScheme point
          (⟨coverMorphism f, coverMorphism_over f⟩ :
            OrbicurveFiniteEtaleCoverMap A B)

/-- The finite type of the actual geometric fiber, under the strict data. -/
noncomputable def fiberFintypeCat
    (baseScheme : SchemeOverField F)
    (point :
      Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor F baseScheme) X.stack.fiber)
    (D : StrictCoverData (F := F) (X := X) baseScheme point)
    (cover : OrbicurveFiniteEtaleCover X) : FintypeCat.{u} :=
  letI : Fintype (GeomFiber baseScheme point cover) := D.fintype cover
  FintypeCat.of (GeomFiber baseScheme point cover)

/-- The actual geometric fiber functor, conditional on the strict cover
data.  Its objects are the actual geometric fibers and its morphisms are the
actual geometric-fiber maps; the only inputs beyond the geometric point are the
strict identity/composition laws, which the 2-category does not provide. -/
noncomputable def geometricFiberFunctor
    (baseScheme : SchemeOverField F)
    (point :
      Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor F baseScheme) X.stack.fiber)
    (D : StrictCoverData (F := F) (X := X) baseScheme point) :
    OrbicurveFiniteEtaleCover X ⥤ FintypeCat.{u} where
  obj cover := fiberFintypeCat baseScheme point D cover
  map {A B} f :=
    FintypeCat.homMk
      (geomFiberMap baseScheme point
        (⟨D.coverMorphism f, D.coverMorphism_over f⟩ :
          OrbicurveFiniteEtaleCoverMap A B))
  map_id A := by
    apply FintypeCat.hom_ext
    intro x
    exact congrFun (D.map_id A) x
  map_comp {A B C} f g := by
    apply FintypeCat.hom_ext
    intro x
    exact congrFun (D.map_comp f g) x

@[simp] theorem geometricFiberFunctor_obj
    (baseScheme : SchemeOverField F)
    (point :
      Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor F baseScheme) X.stack.fiber)
    (D : StrictCoverData (F := F) (X := X) baseScheme point)
    (cover : OrbicurveFiniteEtaleCover X) :
    (geometricFiberFunctor baseScheme point D).obj cover =
      fiberFintypeCat baseScheme point D cover := rfl

@[simp] theorem geometricFiberFunctor_map_apply
    (baseScheme : SchemeOverField F)
    (point :
      Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor F baseScheme) X.stack.fiber)
    (D : StrictCoverData (F := F) (X := X) baseScheme point)
    {A B : OrbicurveFiniteEtaleCover X} (f : A ⟶ B)
    (x : GeomFiber baseScheme point A) :
    (geometricFiberFunctor baseScheme point D).map f x =
      geomFiberMap baseScheme point
        (⟨D.coverMorphism f, D.coverMorphism_over f⟩ :
          OrbicurveFiniteEtaleCoverMap A B) x := rfl

end CoverCategory

end LeanFormal.IUT.XiFPaper.S1735Core
