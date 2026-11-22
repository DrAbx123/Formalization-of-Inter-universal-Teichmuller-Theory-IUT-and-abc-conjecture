import Iut.Foundations.Orbicurve
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import tmp.sheaf.xif.paper.S1631SmallCoverCategoryActual

-- S1641: actual composition of finite-etale cover maps over an orbicurve.
--
-- S1631 recorded that the composition
--   CoverMap A B -> CoverMap B C -> CoverMap A C
-- was missing, and that without it no category structure on the cover maps
-- can be written.  Here we construct that composition from the actual data
--   map : source.source.Hom target.source        (a strong transformation)
--   commutes : Iso (vcomp map target.map) source.map
-- using the associator and left-whiskering isomorphisms of the bicategory
-- of pseudofunctors  LocallyDiscrete (Sch/F)^op to Cat.
--
-- We also prove:
--   * the component formula for the composite commuting 2-cell (it is exactly
--     the associator, then the whiskered old 2-cell, then the new 2-cell);
--   * the corresponding formula on inverse 2-cells;
--   * the naive CategoryStruct on covers (id and composition);
--   * that the categorical identity/associativity laws would force strictness
--     of the pseudofunctor unitors/associator, i.e. 1-morphism *equalities*
--     where the bicategorical data only supplies 2-isomorphisms.  These
--     strict equalities are recorded as necessary conditions and as the exact
--     first missing 2-cell coherence; no Category instance is fabricated, and
--     no Shrink/ULift/small carrier is introduced.
--
-- Result: actual composition and its commuting 2-cell are constructed
-- (EXIT=0).  The naive CategoryStruct on covers is written (id + comp), but no
-- Category instance is produced.  Its three law targets are
-- S1641IdCompLaw / S1641CompIdLaw / S1641AssocLaw; any proof of them forces
-- the strict 1-morphism equalities S1641StrictLeftUnitor /
-- S1641StrictRightUnitor / S1641StrictAssociator, which the available
-- pseudofunctor associator/unitor data gives only as 2-isomorphisms.  The
-- original Category.{0,1} field is missing for two independent reasons:
-- (i) Hom carrier: OrbicurveFiniteEtaleCoverMap is Type 1, not Type 0
--     (S1562/S1566/S1631, no Shrink/ULift carrier is introduced);
-- (ii) coherence: the raw cover maps are 1-morphisms of a bicategory, so the
--     categorical laws need the strict unitors/associators above.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut

universe u

variable {F : Type u} [Field F]
variable {X : HyperbolicOrbicurve F}

/-- The associator 2-cell for the underlying strong transformations of two
composable cover maps.  Its source is the composition of the three
1-morphisms, its target is the reassociated composition. -/
noncomputable def S1641CoverMapAssociator
    {A B C : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B)
    (g : OrbicurveFiniteEtaleCoverMap B C) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp f.map g.map) C.map)
      (Pseudofunctor.StrongTrans.vcomp
        f.map (Pseudofunctor.StrongTrans.vcomp g.map C.map)) := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A.source.fiber
  let mid1 : Bicat := B.source.fiber
  let mid2 : Bicat := C.source.fiber
  let target : Bicat := X.stack.fiber
  let fmap : source ⟶ mid1 := f.map
  let gmap : mid1 ⟶ mid2 := g.map
  let cmap : mid2 ⟶ target := C.map
  exact Pseudofunctor.StrongTrans.associator fmap gmap cmap

/-- Left whiskering by the first cover map of the commuting 2-cell of the
second cover map.  This is the middle 2-cell of the composite comparison. -/
noncomputable def S1641CoverMapWhisker
    {A B C : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B)
    (g : OrbicurveFiniteEtaleCoverMap B C) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        f.map (Pseudofunctor.StrongTrans.vcomp g.map C.map))
      (Pseudofunctor.StrongTrans.vcomp f.map B.map) := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  let source : Bicat := A.source.fiber
  let mid1 : Bicat := B.source.fiber
  let mid2 : Bicat := C.source.fiber
  let target : Bicat := X.stack.fiber
  let fmap : source ⟶ mid1 := f.map
  let gmap : mid1 ⟶ mid2 := g.map
  let cmap : mid2 ⟶ target := C.map
  let tmap : mid1 ⟶ target := B.map
  exact @Bicategory.whiskerLeftIso Bicat _
    source mid1 target fmap (gmap ≫ cmap) tmap g.commutes

/-- The commuting 2-cell of the composite cover map: reassociate, then whisker
the second comparison, then compose with the first comparison. -/
noncomputable def S1641CoverMapCompCommutes
    {A B C : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B)
    (g : OrbicurveFiniteEtaleCoverMap B C) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp f.map g.map) C.map)
      A.map :=
  (S1641CoverMapAssociator f g).trans
    ((S1641CoverMapWhisker f g).trans f.commutes)

/-- Actual composition of cover maps, matching the target 2-cell. -/
noncomputable def S1641CoverMapComp
    {A B C : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B)
    (g : OrbicurveFiniteEtaleCoverMap B C) :
    OrbicurveFiniteEtaleCoverMap A C where
  map := Pseudofunctor.StrongTrans.vcomp f.map g.map
  commutes := S1641CoverMapCompCommutes f g

/-- Actual identity cover map, matching the target 2-cell via the left
unitor of the bicategory of pseudofunctors. -/
noncomputable def S1641CoverMapId (A : OrbicurveFiniteEtaleCover X) :
    OrbicurveFiniteEtaleCoverMap A A where
  map := Pseudofunctor.StrongTrans.id A.source.fiber
  commutes := by
    let Bicat := EtaleStackPseudofunctor F
    letI : Bicategory Bicat := inferInstance
    let source : Bicat := A.source.fiber
    let target : Bicat := X.stack.fiber
    let amap : source ⟶ target := A.map
    exact Pseudofunctor.StrongTrans.leftUnitor amap

@[simp]
theorem S1641CoverMapComp_map
    {A B C : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B)
    (g : OrbicurveFiniteEtaleCoverMap B C) :
    (S1641CoverMapComp f g).map =
      Pseudofunctor.StrongTrans.vcomp f.map g.map := rfl

@[simp]
theorem S1641CoverMapId_map (A : OrbicurveFiniteEtaleCover X) :
    (S1641CoverMapId A).map = Pseudofunctor.StrongTrans.id A.source.fiber := rfl

/-- The composite comparison 2-cell is, on components, the associator followed
by the whiskered comparison of the second map and the comparison of the first
map.  This is the form in which the composite commutes with the target
2-cell. -/
theorem S1641CoverMapComp_commutes_hom_app
    {A B C : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B)
    (g : OrbicurveFiniteEtaleCoverMap B C)
    (a : LocallyDiscrete (SchemeOverField F)ᵒᵖ) :
    (S1641CoverMapCompCommutes f g).hom.as.app a =
      (Pseudofunctor.StrongTrans.associator f.map g.map C.map).hom.as.app a ≫
        (f.map.app a ◁ (g.commutes.hom.as.app a)) ≫
          f.commutes.hom.as.app a := rfl

/-- The inverse component formula. -/
theorem S1641CoverMapComp_commutes_inv_app
    {A B C : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B)
    (g : OrbicurveFiniteEtaleCoverMap B C)
    (a : LocallyDiscrete (SchemeOverField F)ᵒᵖ) :
    (S1641CoverMapCompCommutes f g).inv.as.app a =
      (f.commutes.inv.as.app a ≫
        (f.map.app a ◁ (g.commutes.inv.as.app a))) ≫
          (Pseudofunctor.StrongTrans.associator f.map g.map C.map).inv.as.app a := rfl

/-- The target decomposition of the composite comparison: it is exactly the
associator, the whiskered comparison of the second map, and the comparison of
the first map. -/
theorem S1641CoverMapComp_commutes_decomposition
    {A B C : OrbicurveFiniteEtaleCover X}
    (f : OrbicurveFiniteEtaleCoverMap A B)
    (g : OrbicurveFiniteEtaleCoverMap B C) :
    (S1641CoverMapComp f g).commutes =
      (S1641CoverMapAssociator f g).trans
        ((S1641CoverMapWhisker f g).trans f.commutes) := rfl

/-- The naive category structure on covers, using the actual composition and
identity constructed above. -/
@[reducible] noncomputable def S1641CoverCategoryStruct :
    CategoryStruct (OrbicurveFiniteEtaleCover X) where
  Hom := OrbicurveFiniteEtaleCoverMap
  id := S1641CoverMapId
  comp := S1641CoverMapComp

/-- Left identity law for the naive category structure, written on the actual
composition and identity. -/
def S1641IdCompLaw : Prop :=
  ∀ (A B : OrbicurveFiniteEtaleCover X)
    (f : OrbicurveFiniteEtaleCoverMap A B),
    S1641CoverMapComp (S1641CoverMapId A) f = f

/-- Right identity law. -/
def S1641CompIdLaw : Prop :=
  ∀ (A B : OrbicurveFiniteEtaleCover X)
    (f : OrbicurveFiniteEtaleCoverMap A B),
    S1641CoverMapComp f (S1641CoverMapId B) = f

/-- Associativity law. -/
def S1641AssocLaw : Prop :=
  ∀ (A B C D : OrbicurveFiniteEtaleCover X)
    (f : OrbicurveFiniteEtaleCoverMap A B)
    (g : OrbicurveFiniteEtaleCoverMap B C)
    (h : OrbicurveFiniteEtaleCoverMap C D),
    S1641CoverMapComp (S1641CoverMapComp f g) h =
      S1641CoverMapComp f (S1641CoverMapComp g h)

/-- The strict left unitor equality: the underlying 1-morphism equality forced
(necessarily, not sufficiently) by the categorical left identity law. -/
def S1641StrictLeftUnitor : Prop :=
  ∀ (A B : OrbicurveFiniteEtaleCover X)
    (f : OrbicurveFiniteEtaleCoverMap A B),
    Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.id A.source.fiber) f.map = f.map

/-- The strict right unitor equality. -/
def S1641StrictRightUnitor : Prop :=
  ∀ (A B : OrbicurveFiniteEtaleCover X)
    (f : OrbicurveFiniteEtaleCoverMap A B),
    Pseudofunctor.StrongTrans.vcomp
      f.map (Pseudofunctor.StrongTrans.id B.source.fiber) = f.map

/-- The strict associator equality: the underlying 1-morphism equality forced
(necessarily, not sufficiently) by the categorical associativity law. -/
def S1641StrictAssociator : Prop :=
  ∀ (A B C D : OrbicurveFiniteEtaleCover X)
    (f : OrbicurveFiniteEtaleCoverMap A B)
    (g : OrbicurveFiniteEtaleCoverMap B C)
    (h : OrbicurveFiniteEtaleCoverMap C D),
    Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp f.map g.map) h.map =
      Pseudofunctor.StrongTrans.vcomp
        f.map (Pseudofunctor.StrongTrans.vcomp g.map h.map)

/-- The left identity law forces the strict left unitor equality on maps. -/
theorem S1641IdCompLaw_strictLeftUnitor
    (h : S1641IdCompLaw (F := F) (X := X)) :
    S1641StrictLeftUnitor (F := F) (X := X) := by
  intro A B f
  exact congrArg OrbicurveFiniteEtaleCoverMap.map (h A B f)

/-- The right identity law forces the strict right unitor equality on maps. -/
theorem S1641CompIdLaw_strictRightUnitor
    (h : S1641CompIdLaw (F := F) (X := X)) :
    S1641StrictRightUnitor (F := F) (X := X) := by
  intro A B f
  exact congrArg OrbicurveFiniteEtaleCoverMap.map (h A B f)

/-- The associativity law forces the strict associator equality on maps. -/
theorem S1641AssocLaw_strictAssociator
    (h : S1641AssocLaw (F := F) (X := X)) :
    S1641StrictAssociator (F := F) (X := X) := by
  intro A B C D f g hgh
  exact congrArg OrbicurveFiniteEtaleCoverMap.map (h A B C D f g hgh)

/-- The full categorical structure at the matching universe.  This is the
faithful universe-corrected interface; its obstruction is the strictness
coherence recorded above. -/
def S1641Category11Required : Type (u + 2) :=
  Category.{u + 1, u + 1} (OrbicurveFiniteEtaleCover X)

/-- The original interface field, with Type 0 hom types. -/
def S1641Category01Required : Type (u + 1) :=
  Category.{0, u + 1} (OrbicurveFiniteEtaleCover X)

/-- A Type 0 hom carrier equivalent to the actual cover maps, the first
missing datum for the original small interface.  No Shrink/ULift carrier is
provided. -/
structure S1641SmallHomData where
  Hom : OrbicurveFiniteEtaleCover X → OrbicurveFiniteEtaleCover X → Type
  homEquiv : ∀ A B : OrbicurveFiniteEtaleCover X,
    Hom A B ≃ OrbicurveFiniteEtaleCoverMap A B


/-! ## Specialization to the S1631 paper orbicurve

S1631 recorded the exact missing composition functional
`S1631CompositionRequired`.  The construction above inhabits it directly. -/

namespace S1641Paper

open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1522OrbicurveEtalePiActual
open LeanFormal.IUT.XiFPaper.S1562CoverCategoryUniverseActual
open LeanFormal.IUT.XiFPaper.S1631SmallCoverCategoryActual

variable (l : PrimeGeFive)

/-- The actual composition required by S1631, for the paper orbicurve. -/
noncomputable def S1641S1631Composition :
    S1631CompositionRequired (l := l) :=
  fun A B C f g =>
    S1641CoverMapComp (F := S1348K l) (X := S1562Orbicurve (l := l)) f g

/-- The identity constructed here is the S1631/S405 identity map. -/
theorem S1641S1631Id_eq (A : S1631Cover (l := l)) :
    S1641CoverMapId (F := S1348K l) (X := S1562Orbicurve (l := l)) A =
      S1631Id (l := l) A := rfl

/-- The paper-level associativity law is still exactly the strictness
coherence recorded above. -/
theorem S1641S1631AssocLaw_strictAssociator
    (h : S1641AssocLaw (F := S1348K l) (X := S1562Orbicurve (l := l))) :
    S1641StrictAssociator (F := S1348K l) (X := S1562Orbicurve (l := l)) :=
  S1641AssocLaw_strictAssociator h

#check S1641S1631Composition
#check S1641S1631Id_eq
#print axioms S1641S1631Composition
#print axioms S1641S1631Id_eq

end S1641Paper

#check S1641CoverMapComp
#check S1641CoverMapId
#check S1641CoverMapAssociator
#check S1641CoverMapWhisker
#check S1641CoverMapComp_commutes_hom_app
#check S1641CoverMapComp_commutes_inv_app
#check S1641CoverMapComp_commutes_decomposition
#check S1641CoverCategoryStruct
#check S1641IdCompLaw
#check S1641CompIdLaw
#check S1641AssocLaw
#check S1641IdCompLaw_strictLeftUnitor
#check S1641CompIdLaw_strictRightUnitor
#check S1641AssocLaw_strictAssociator
#check S1641Category11Required
#check S1641Category01Required
#check S1641SmallHomData
#print axioms S1641CoverMapComp
#print axioms S1641CoverMapComp_commutes_hom_app
#print axioms S1641IdCompLaw_strictLeftUnitor

end LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual

end
