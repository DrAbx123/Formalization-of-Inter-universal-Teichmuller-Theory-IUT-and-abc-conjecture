import tmp.sheaf.xif.paper.S2517CoverEquivObjectActual
import tmp.sheaf.xif.paper.S2512StackOpenImmersionUB

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2512StackOpenImmersionUB
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual

/-- The base scheme of S2482 as an F-scheme. -/
abbrev S2517S : Iut.SchemeOverField F := S2482AffineOver

/-- The underlying scheme of the base. -/
abbrev S2517BaseScheme : Scheme := S2482AffineOver.left

/-- A finite etale cover of the S2482 affine scheme, viewed as an F-scheme. -/
abbrev S2517CScheme (C : FiniteEtaleCover S2482AffineScheme) : Iut.SchemeOverField F :=
  let f : C.obj.left ⟶ S2517BaseScheme := C.obj.hom
  Over.mk (f ≫ S2482AffineOver.hom)

/-- The scheme-valued point corresponding to a strong transformation. -/
noncomputable def S2517G (T : Iut.SchemeOverField F)
    (q : Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F T)
      (Iut.schemeRepresentableEtalePseudofunctor F S2517S)) : T ⟶ S2517S :=
  S1742HomOfStrongTrans q

/-- The scheme pullback of a finite etale cover along a point. -/
noncomputable def S2517PullbackScheme (C : FiniteEtaleCover S2482AffineScheme)
    (T : Iut.SchemeOverField F)
    (q : Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F T)
      (Iut.schemeRepresentableEtalePseudofunctor F S2517S)) : Iut.SchemeOverField F :=
  let g : T.left ⟶ S2517BaseScheme := (S2517G T q).left
  Over.mk (pullback.fst C.obj.hom g ≫ C.obj.hom ≫ S2482AffineOver.hom)

/-- Projection of the pullback to the test scheme. -/
noncomputable def S2517Projection (C : FiniteEtaleCover S2482AffineScheme)
    (T : Iut.SchemeOverField F)
    (q : Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F T)
      (Iut.schemeRepresentableEtalePseudofunctor F S2517S)) :
    S2517PullbackScheme C T q ⟶ T :=
  let f : C.obj.left ⟶ S2517BaseScheme := C.obj.hom
  let g : T.left ⟶ S2517BaseScheme := (S2517G T q).left
  Over.homMk (pullback.snd f g) (by
    change pullback.snd f g ≫ T.hom =
      pullback.fst f g ≫ f ≫ S2482AffineOver.hom
    rw [← Category.assoc, pullback.condition, Category.assoc]
    have hg : g ≫ S2482AffineOver.hom = T.hom := by
      simpa [S2517BaseScheme, S2517S, S2517G, f, g] using (S2517G T q).w
    simpa [Category.assoc, ← hg])

#check S2517PullbackScheme
#check S2517Projection

/-- The cover map as a morphism of F-schemes. -/
noncomputable def S2517OverMap (C : FiniteEtaleCover S2482AffineScheme) :
    S2517CScheme C ⟶ S2517S :=
  Over.homMk C.obj.hom (by
    change C.obj.hom ≫ S2482AffineOver.hom =
      C.obj.hom ≫ S2482AffineOver.hom
    rfl)

/-- Projection of the fibre product to the cover. -/
noncomputable def S2517ToSource (C : FiniteEtaleCover S2482AffineScheme)
    (T : Iut.SchemeOverField F)
    (q : Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F T)
      (Iut.schemeRepresentableEtalePseudofunctor F S2517S)) :
    S2517PullbackScheme C T q ⟶ S2517CScheme C :=
  let f : C.obj.left ⟶ S2517BaseScheme := C.obj.hom
  let g : T.left ⟶ S2517BaseScheme := (S2517G T q).left
  Over.homMk (pullback.fst f g) (by
    change pullback.fst f g ≫ (f ≫ S2482AffineOver.hom) =
      (pullback.fst f g ≫ f) ≫ S2482AffineOver.hom
    rw [Category.assoc])

/-- The projection map as a represented map. -/
noncomputable def S2517ProjectionMap (C : FiniteEtaleCover S2482AffineScheme)
    (T : Iut.SchemeOverField F)
    (q : Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F T)
      (Iut.schemeRepresentableEtalePseudofunctor F S2517S)) :
    Iut.SchemeRepresentableMap (S2517Projection C T q) where
  transformation := S1742StrongTransOfHom (S2517Projection C T q)
  app_eq := by
    intro U
    rfl

#check S2517ToSource
#check S2517ProjectionMap

/-- Underlying scheme pullback condition. -/
theorem S2517SquareCommutesHom (C : FiniteEtaleCover S2482AffineScheme)
    (T : Iut.SchemeOverField F)
    (q : Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F T)
      (Iut.schemeRepresentableEtalePseudofunctor F S2517S)) :
    (S2517ToSource C T q).left ≫ C.obj.hom =
      (S2517Projection C T q).left ≫ (S2517G T q).left := by
  change pullback.fst C.obj.hom (S2517G T q).left ≫ C.obj.hom =
    pullback.snd C.obj.hom (S2517G T q).left ≫ (S2517G T q).left
  exact pullback.condition

/-- The comparison 2-isomorphism of the representable base-change square. -/
noncomputable def S2517Commutes (C : FiniteEtaleCover S2482AffineScheme)
    (T : Iut.SchemeOverField F)
    (q : Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F T)
      (Iut.schemeRepresentableEtalePseudofunctor F S2517S)) :
    Iso
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := F) (S2517ToSource C T q))
        (S1742StrongTransOfHom (F := F) (S2517OverMap C)))
      (Pseudofunctor.StrongTrans.vcomp
        (S2517ProjectionMap C T q).transformation q) :=
  (S2512Val_isoOfValEq (F := F) (T := S2517S)
    (L := Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := F) (S2517ToSource C T q))
      (S1742StrongTransOfHom (F := F) (S2517OverMap C)))
    (L' := Pseudofunctor.StrongTrans.vcomp
      (S2517ProjectionMap C T q).transformation q)
    (fun U a => by
      rcases a with ⟨P⟩
      ext
      let f : C.obj.left ⟶ S2517BaseScheme := C.obj.hom
      let g : T.left ⟶ S2517BaseScheme := (S2517G T q).left
      let pr : S2517PullbackScheme C T q ⟶ T := S2517Projection C T q
      simp only [S2517ProjectionMap, S2512Val_vcomp, S2512Val_strongTransOfHom,
        S1742HomOfStrongTrans_strongTransOfHom, S2517OverMap, S2517G, Over.comp_left]
      change (Over.Hom.left P ≫ (S2517ToSource C T q).left) ≫ C.obj.hom =
        (Over.Hom.left P ≫ (S2517Projection C T q).left) ≫ (S2517G T q).left
      rw [Category.assoc, Category.assoc, S2517SquareCommutesHom]
      rfl)).some

#check S2517SquareCommutesHom
#check S2517Commutes


end LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
end
