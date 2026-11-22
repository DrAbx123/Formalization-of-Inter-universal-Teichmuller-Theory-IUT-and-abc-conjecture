import tmp.sheaf.xif.paper.S3127CoverMorphismActual
import tmp.sheaf.xif.paper.S1742HomVcompActual
import tmp.sheaf.xif.paper.S3121StrongTransVcompActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveGaloisCategory
import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.RepresentableCoverChosenCategoryActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual
open LeanFormal.IUT.XiFPaper.S3121StrongTransVcompActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127ForgetfulActual
variable {l : PrimeGeFive}

noncomputable def S3127FiniteEtaleObj (A : S3127Cover (l := l)) :
    FiniteEtaleCover (S1419AffineScheme l) := by
  let f := S1742HomOfStrongTrans (F := S1348K l) A.map
  let O : Over (S1419AffineScheme l) := Over.mk f.left
  refine ⟨O, ?_⟩
  show Etale f.left ∧ IsFinite f.left
  exact ⟨A.finiteEtale.2, A.finiteEtale.1⟩

noncomputable def S3127FiniteEtaleMap {A B : S3127Cover (l := l)}
    (φ : S3127RepMap A B) :
    S3127FiniteEtaleObj A ⟶ S3127FiniteEtaleObj B := by
  let fA := S1742HomOfStrongTrans (F := S1348K l) A.map
  let fB := S1742HomOfStrongTrans (F := S1348K l) B.map
  have h : φ.hom ≫ fB = fA := by
    have hc := S1742HomOfStrongTrans_congr (F := S1348K l) φ.commutes.some
    change S1742HomOfStrongTrans (F := S1348K l)
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1348K l) φ.hom) B.map) =
        S1742HomOfStrongTrans (F := S1348K l) A.map at hc
    rwa [S1742HomOfStrongTrans_vcomp,
      S1742HomOfStrongTrans_strongTransOfHom] at hc
  have hleft : φ.hom.left ≫ fB.left = fA.left := by
    simpa using congrArg (fun k : A.scheme ⟶ S1419AffineOver (l := l) => k.left) h
  exact ObjectProperty.homMk
    (Over.homMk (U := (S3127FiniteEtaleObj A).obj)
      (V := (S3127FiniteEtaleObj B).obj) φ.hom.left (by
        exact hleft))

noncomputable def S3127ForgetFunctor :
    S3127Cover (l := l) ⥤ FiniteEtaleCover (S1419AffineScheme l) where
  obj := S3127FiniteEtaleObj
  map := S3127FiniteEtaleMap
  map_id A := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl

structure S3127FreeAction (A : S3127Cover (l := l))
    (G : Type) [Group G] [Fintype G] : Type where
  action : G → S3127RepMap A A
  action_one : action 1 = S3127Id A
  action_mul : ∀ g h : G,
    action (g * h) = S3127Comp (action g) (action h)
  free : ∀ (x : A.scheme.left) (g : G),
    (action g).hom.left x = x → g = 1

structure S3127FreeFiniteEtaleQuotientTarget
    (A : S3127Cover (l := l)) (G : Type) [Group G] [Fintype G] : Type 2 where
  freeAction : S3127FreeAction A G
  quotient : S3127Cover (l := l)
  quotientMap : S3127RepMap A quotient
  invariant : ∀ g : G,
    S3127Comp (freeAction.action g) quotientMap = quotientMap
  desc : ∀ {B : S3127Cover (l := l)} (f : S3127RepMap A B),
    (∀ g : G, S3127Comp (freeAction.action g) f = f) →
      S3127RepMap quotient B
  fac : ∀ {B : S3127Cover (l := l)} (f : S3127RepMap A B)
    (hf : ∀ g : G, S3127Comp (freeAction.action g) f = f),
    S3127Comp quotientMap (desc f hf) = f
  uniq : ∀ {B : S3127Cover (l := l)} (f : S3127RepMap A B)
    (hf : ∀ g : G, S3127Comp (freeAction.action g) f = f)
    (v : S3127RepMap quotient B),
    S3127Comp quotientMap v = f → v = desc f hf

theorem S3127ForgetFunctor_map_injective {A B : S3127Cover (l := l)} :
    Function.Injective
      ((S3127ForgetFunctor (l := l)).map (X := A) (Y := B)) := by
  intro φ ψ h
  have hleft : φ.hom.left = ψ.hom.left := by
    have := congrArg
      (fun k : S3127FiniteEtaleObj A ⟶ S3127FiniteEtaleObj B =>
        k.hom.left) h
    exact this
  have hhom : φ.hom = ψ.hom := by
    apply Over.OverMorphism.ext
    exact hleft
  exact S3127RepMap_ext φ ψ hhom

noncomputable instance S3127ForgetFunctor_faithful :
    (S3127ForgetFunctor (l := l)).Faithful where
  map_injective := fun {X Y} f g h =>
    S3127ForgetFunctor_map_injective (A := X) (B := Y) h

/-- K-linear target: finite etale covers of S1419 inside SchemeOverField K. -/
structure S3127FiniteEtaleOverK where
  obj : Over (S1419AffineOver (l := l))
  finiteEtale : IsFinite obj.hom.left ∧ Etale obj.hom.left

noncomputable instance S3127FiniteEtaleOverK_category :
    Category (S3127FiniteEtaleOverK (l := l)) where
  Hom A B := A.obj ⟶ B.obj
  id A := 𝟙 A.obj
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

noncomputable def S3127KLinearObj (A : S3127Cover (l := l)) :
    S3127FiniteEtaleOverK (l := l) where
  obj := Over.mk (S1742HomOfStrongTrans (F := S1348K l) A.map)
  finiteEtale := ⟨A.finiteEtale.1, A.finiteEtale.2⟩

noncomputable def S3127KLinearMap {A B : S3127Cover (l := l)}
    (φ : S3127RepMap A B) :
    S3127KLinearObj A ⟶ S3127KLinearObj B := by
  let fA := S1742HomOfStrongTrans (F := S1348K l) A.map
  let fB := S1742HomOfStrongTrans (F := S1348K l) B.map
  have h : φ.hom ≫ fB = fA := by
    have hc := S1742HomOfStrongTrans_congr (F := S1348K l) φ.commutes.some
    change S1742HomOfStrongTrans (F := S1348K l)
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1348K l) φ.hom) B.map) =
        S1742HomOfStrongTrans (F := S1348K l) A.map at hc
    rwa [S1742HomOfStrongTrans_vcomp,
      S1742HomOfStrongTrans_strongTransOfHom] at hc
  exact Over.homMk φ.hom h

noncomputable def S3127KLinearFunctor :
    S3127Cover (l := l) ⥤ S3127FiniteEtaleOverK (l := l) where
  obj := S3127KLinearObj
  map := S3127KLinearMap
  map_id A := by
    apply Over.OverMorphism.ext
    rfl
  map_comp f g := by
    apply Over.OverMorphism.ext
    rfl

noncomputable def S3127RepMapOfKLinear {A B : S3127Cover (l := l)}
    (f : S3127KLinearObj A ⟶ S3127KLinearObj B) :
    S3127RepMap A B where
  hom := f.left
  commutes := by
    let fA := S1742HomOfStrongTrans (F := S1348K l) A.map
    let fB := S1742HomOfStrongTrans (F := S1348K l) B.map
    let eB := S1742StrongTransIsoOfHom (F := S1348K l) B.map
    let w := Bicategory.whiskerLeftIso
      (a := S1742YS (F := S1348K l) A.scheme)
      (b := S1742YS (F := S1348K l) B.scheme)
      (c := (S1536XF (l := l)).stack.fiber)
      (S1742StrongTransOfHom (F := S1348K l) f.left) eB
    have hcomp : Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := S1348K l) f.left)
        (S1742StrongTransOfHom (F := S1348K l) fB) =
        S1742StrongTransOfHom (F := S1348K l) (f.left ≫ fB) :=
      S3121StrongTransOfHom_vcomp (S1348K l) f.left fB
    have hsq : f.left ≫ fB = fA := f.w
    refine ⟨w.symm.trans ((eqToIso hcomp).trans
      ((eqToIso (congrArg (fun k => S1742StrongTransOfHom (F := S1348K l) k) hsq)).trans
        (S1742StrongTransIsoOfHom (F := S1348K l) A.map)))⟩

noncomputable instance S3127KLinearFunctor_full :
    (S3127KLinearFunctor (l := l)).Full where
  map_surjective := by
    intro A B f
    exact ⟨S3127RepMapOfKLinear f, by
      apply Over.OverMorphism.ext
      rfl⟩

theorem S3127KLinearFunctor_map_injective {A B : S3127Cover (l := l)} :
    Function.Injective
      ((S3127KLinearFunctor (l := l)).map (X := A) (Y := B)) := by
  intro φ ψ h
  have hhom : φ.hom = ψ.hom := by
    have := congrArg
      (fun k : S3127KLinearObj A ⟶ S3127KLinearObj B => k.left) h
    exact this
  exact S3127RepMap_ext φ ψ hhom

noncomputable instance S3127KLinearFunctor_faithful :
    (S3127KLinearFunctor (l := l)).Faithful where
  map_injective := fun {X Y} f g h =>
    S3127KLinearFunctor_map_injective (A := X) (B := Y) h

/-- From a K-linear finite etale cover build an S3127Cover via 2-Yoneda. -/
noncomputable def S3127CoverOfKLinear
    (Y : S3127FiniteEtaleOverK (l := l)) :
    S3127Cover (l := l) where
  scheme := Y.obj.left
  map := S1742StrongTransOfHom (F := S1348K l) Y.obj.hom
  finiteEtale := Y.finiteEtale

theorem S3127KLinearObj_coverOfKLinear
    (Y : S3127FiniteEtaleOverK (l := l)) :
    S3127KLinearObj (S3127CoverOfKLinear Y) = Y := by
  cases Y with
  | mk obj prop =>
    cases obj with
    | mk X f =>
      rfl

noncomputable instance S3127KLinearFunctor_essSurj :
    (S3127KLinearFunctor (l := l)).EssSurj where
  mem_essImage Y :=
    ⟨S3127CoverOfKLinear Y,
      ⟨eqToIso (S3127KLinearObj_coverOfKLinear Y)⟩⟩

noncomputable instance S3127KLinearFunctor_isEquivalence :
    (S3127KLinearFunctor (l := l)).IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := inferInstance

noncomputable def S3127KLinearEquivalence :
    S3127Cover (l := l) ≌ S3127FiniteEtaleOverK (l := l) :=
  (S3127KLinearFunctor (l := l)).asEquivalence

#check S3127KLinearObj_coverOfKLinear
#check S3127KLinearFunctor_essSurj
#check S3127KLinearEquivalence

noncomputable def S3127FiniteEtaleOverK.ofOpens
    (Y : S3127FiniteEtaleOverK (l := l))
    (U : Y.obj.left.left.Opens)
    (hfin : IsFinite (U.ι ≫ Y.obj.hom.left))
    (het : Etale (U.ι ≫ Y.obj.hom.left)) :
    S3127FiniteEtaleOverK (l := l) where
  obj := by
    let Uover : Over (Spec (CommRingCat.of (S1348K l))) :=
      Over.mk (U.ι ≫ Y.obj.left.hom)
    let homOver : Uover ⟶ S1419AffineOver (l := l) :=
      Over.homMk (U := Uover) (V := S1419AffineOver (l := l))
        (U.ι ≫ Y.obj.hom.left) (by
          change (U.ι ≫ Y.obj.hom.left) ≫ Over.hom (S1419AffineOver (l := l)) =
            Over.hom Uover
          rw [Category.assoc, Y.obj.hom.w]
          rfl)
    exact Over.mk homOver
  finiteEtale := by
    change IsFinite (U.ι ≫ Y.obj.hom.left) ∧
      Etale (U.ι ≫ Y.obj.hom.left)
    exact ⟨hfin, het⟩

noncomputable def S3127KLinearFiniteEtaleObj
    (Y : S3127FiniteEtaleOverK (l := l)) :
    FiniteEtaleCover (S1419AffineScheme l) :=
  ⟨Over.mk Y.obj.hom.left, ⟨Y.finiteEtale.2, Y.finiteEtale.1⟩⟩

noncomputable def S3127KLinearFiniteEtaleMap
    {A B : S3127FiniteEtaleOverK (l := l)} (f : A ⟶ B) :
    S3127KLinearFiniteEtaleObj A ⟶ S3127KLinearFiniteEtaleObj B := by
  exact ObjectProperty.homMk
    (Over.homMk (U := (S3127KLinearFiniteEtaleObj A).obj)
      (V := (S3127KLinearFiniteEtaleObj B).obj)
      f.left.left (by
        have h := congrArg
          (fun k : A.obj.left ⟶ S1419AffineOver (l := l) =>
            Over.Hom.left k) (Over.w f)
        rw [Over.comp_left] at h
        change Over.Hom.left (Over.Hom.left f) ≫
          Over.Hom.left B.obj.hom = Over.Hom.left A.obj.hom
        exact h))

noncomputable def S3127KLinearToFiniteEtaleFunctor :
    S3127FiniteEtaleOverK (l := l) ⥤
      FiniteEtaleCover (S1419AffineScheme l) where
  obj := S3127KLinearFiniteEtaleObj
  map := S3127KLinearFiniteEtaleMap
  map_id A := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl

noncomputable def S3127KLinearComplementOpens
    {X Y : S3127FiniteEtaleOverK (l := l)}
    (j : S3127KLinearFiniteEtaleObj X ⟶ S3127KLinearFiniteEtaleObj Y)
    [Mono j] : Y.obj.left.left.Opens :=
  finiteEtaleCoverMonoComplementOpens j

theorem S3127KLinearComplement_hfin
    {X Y : S3127FiniteEtaleOverK (l := l)}
    (j : S3127KLinearFiniteEtaleObj X ⟶ S3127KLinearFiniteEtaleObj Y)
    [Mono j] :
    IsFinite ((S3127KLinearComplementOpens j).ι ≫ Y.obj.hom.left) := by
  change IsFinite (finiteEtaleCoverMonoComplementStructureMap j)
  exact finiteEtaleCoverMonoComplementStructureMap_isFinite j

theorem S3127KLinearComplement_het
    {X Y : S3127FiniteEtaleOverK (l := l)}
    (j : S3127KLinearFiniteEtaleObj X ⟶ S3127KLinearFiniteEtaleObj Y)
    [Mono j] :
    Etale ((S3127KLinearComplementOpens j).ι ≫ Y.obj.hom.left) := by
  change Etale (finiteEtaleCoverMonoComplementStructureMap j)
  exact finiteEtaleCoverMonoComplementStructureMap_etale j

noncomputable def S3127KLinearComplement
    {X Y : S3127FiniteEtaleOverK (l := l)}
    (j : S3127KLinearFiniteEtaleObj X ⟶ S3127KLinearFiniteEtaleObj Y)
    [Mono j] : S3127FiniteEtaleOverK (l := l) :=
  Y.ofOpens (S3127KLinearComplementOpens j)
    (S3127KLinearComplement_hfin j) (S3127KLinearComplement_het j)

noncomputable def S3127CoverComplement
    {X Y : S3127FiniteEtaleOverK (l := l)}
    (j : S3127KLinearFiniteEtaleObj X ⟶ S3127KLinearFiniteEtaleObj Y)
    [Mono j] : S3127Cover (l := l) :=
  S3127CoverOfKLinear (S3127KLinearComplement j)

#check S3127KLinearComplement
#check S3127CoverComplement
#check S3127KLinearComplement_hfin
end LeanFormal.IUT.XiFPaper.S3127ForgetfulActual
end
