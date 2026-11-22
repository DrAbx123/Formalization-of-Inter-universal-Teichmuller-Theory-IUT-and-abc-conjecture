import tmp.sheaf.xif.paper.S3121StrongTransVcompActual
import tmp.sheaf.xif.paper.S3119StrongTransEqActual
import tmp.sheaf.xif.paper.S1536SourceSignQuotientFromOrbicurveActual
import tmp.sheaf.xif.paper.S2812IsStackActual
import Iut.Foundations.Orbicurve

noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual
open LeanFormal.IUT.XiFPaper.S3119StrongTransEqActual
open LeanFormal.IUT.XiFPaper.S3121StrongTransVcompActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S2812IsStackActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.RepresentableCoverChosenCategoryActual

variable {l : PrimeGeFive}

/-- The representable source stack attached to a chosen scheme. -/
noncomputable def S3127Source (scheme : SchemeOverField (S1348K l)) :
    EtaleStackOverField (S1348K l) where
  fiber := S1742YS (F := S1348K l) scheme
  isStack := schemeRepresentableEtalePseudofunctor_isStack (S1348K l) scheme
  orbicurveSignature := (S1536XF (l := l)).stack.orbicurveSignature

/-- A finite-etale cover of S1536XF with chosen representing scheme. -/
structure S3127Cover where
  scheme : SchemeOverField (S1348K l)
  map : (S3127Source (l := l) scheme).Hom (S1536XF (l := l)).stack
  finiteEtale : AlgebraicGeometry.IsFinite
      (S1742HomOfStrongTrans (F := S1348K l) map).left ∧
    AlgebraicGeometry.Etale
      (S1742HomOfStrongTrans (F := S1348K l) map).left

/-- A raw map between chosen-scheme representable covers.  The commuting
2-isomorphism is recorded as a proposition, so maps with the same underlying
scheme morphism are equal by proof irrelevance. -/
structure S3127RepMap (A B : S3127Cover (l := l)) where
  hom : A.scheme ⟶ B.scheme
  commutes : Nonempty
    (Iso (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S1348K l) hom) B.map) A.map)

/-- Structure extensionality for raw maps, using proof irrelevance for commutes. -/
theorem S3127RepMap_ext {A B : S3127Cover (l := l)}
    (f g : S3127RepMap A B) (h : f.hom = g.hom) : f = g := by
  cases f with
  | mk fh fc =>
    cases g with
    | mk gh gc =>
      cases h
      rfl

/-- Identity raw map. -/
noncomputable def S3127Id (A : S3127Cover (l := l)) : S3127RepMap A A where
  hom := 𝟙 A.scheme
  commutes := by
    let amap : Pseudofunctor.StrongTrans (S1742YS (F := S1348K l) A.scheme)
        (S1536XF (l := l)).stack.fiber := A.map
    let e : S1742StrongTransOfHom (F := S1348K l) (𝟙 A.scheme) =
        Pseudofunctor.StrongTrans.id (S1742YS (F := S1348K l) A.scheme) :=
      S3121StrongTransOfHom_id (F := S1348K l) A.scheme
    exact ⟨(eqToIso (congrArg
      (fun t => Pseudofunctor.StrongTrans.vcomp t amap) e)).trans
        (Pseudofunctor.StrongTrans.leftUnitor amap)⟩

/-- Composition of raw maps. -/
noncomputable def S3127Comp {A B C : S3127Cover (l := l)}
    (f : S3127RepMap A B) (g : S3127RepMap B C) : S3127RepMap A C where
  hom := f.hom ≫ g.hom
  commutes := by
    let amap : Pseudofunctor.StrongTrans (S1742YS (F := S1348K l) A.scheme)
        (S1536XF (l := l)).stack.fiber := A.map
    let bmap : Pseudofunctor.StrongTrans (S1742YS (F := S1348K l) B.scheme)
        (S1536XF (l := l)).stack.fiber := B.map
    let cmap : Pseudofunctor.StrongTrans (S1742YS (F := S1348K l) C.scheme)
        (S1536XF (l := l)).stack.fiber := C.map
    let stf := S1742StrongTransOfHom (F := S1348K l) f.hom
    let stg := S1742StrongTransOfHom (F := S1348K l) g.hom
    have hcomp := S3121StrongTransOfHom_vcomp (F := S1348K l) f.hom g.hom
    let e : Iso (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1348K l) (f.hom ≫ g.hom)) cmap)
        (Pseudofunctor.StrongTrans.vcomp
          (Pseudofunctor.StrongTrans.vcomp stf stg) cmap) :=
      eqToIso (congrArg
        (fun t => Pseudofunctor.StrongTrans.vcomp t cmap) hcomp.symm)
    let gIso : Iso (Pseudofunctor.StrongTrans.vcomp stg cmap) bmap := g.commutes.some
    let fIso : Iso (Pseudofunctor.StrongTrans.vcomp stf bmap) amap := f.commutes.some
    let assoc := Pseudofunctor.StrongTrans.associator stf stg cmap
    let whisk := Bicategory.whiskerLeftIso
      (a := S1742YS (F := S1348K l) A.scheme)
      (b := S1742YS (F := S1348K l) B.scheme)
      (c := (S1536XF (l := l)).stack.fiber) stf gIso
    exact ⟨e.trans (assoc.trans (whisk.trans fIso))⟩

/-- Raw category structure on chosen representable covers. -/
@[reducible] noncomputable def S3127CategoryStruct :
    CategoryStruct (S3127Cover (l := l)) where
  Hom := S3127RepMap
  id := S3127Id
  comp := S3127Comp

/-- The raw Category instance. -/
noncomputable instance S3127Category :
    Category.{0, 1} (S3127Cover (l := l)) where
  toCategoryStruct := S3127CategoryStruct
  id_comp := by
    intro A B f
    apply S3127RepMap_ext
    exact Category.id_comp f.hom
  comp_id := by
    intro A B f
    apply S3127RepMap_ext
    exact Category.comp_id f.hom
  assoc := by
    intro A B C D f g h
    apply S3127RepMap_ext
    exact Category.assoc f.hom g.hom h.hom

#check S3127Cover
#check S3127RepMap
#check S3127Id
#check S3127Comp
#check S3127CategoryStruct
#check S3127Category

end LeanFormal.IUT.XiFPaper.RepresentableCoverChosenCategoryActual
end