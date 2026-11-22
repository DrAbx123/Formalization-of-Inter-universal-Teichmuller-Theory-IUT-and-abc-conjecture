import tmp.sheaf.xif.paper.S2517CoverEquivObjectActual
import tmp.sheaf.xif.paper.S2514IdentityFiniteEtaleActual
import tmp.sheaf.xif.paper.S2398HomOfStrongTransCompActual
import tmp.sheaf.xif.paper.S2482UnderlyingSquareActual
import tmp.sheaf.xif.paper.S1761DMStackSmallnessActual

noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Limits
open Iut
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2398HomOfStrongTransCompActual
open LeanFormal.IUT.XiFPaper.S2482UnderlyingSquareActual
open LeanFormal.IUT.XiFPaper.S1761DMStackSmallnessActual
open LeanFormal.IUT.XiFPaper.S2514IdentityFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2517CoverEquivObjectActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2517CoverEquivMapActual

abbrev S2517YS (T : SchemeOverField F) : EtaleStackPseudofunctor F :=
  Iut.schemeRepresentableEtalePseudofunctor F T

/-- The base-change square of a cover at the identity point. -/
noncomputable def S2517Square (C : S2517Cover) :
    EtalePseudofunctorSquare (S2517YS (C.finiteEtale.baseChange S2482AffineOver S2517Point).pullbackScheme)
      C.source.fiber (S2517YS S2482AffineOver) S2482Orbicurve.stack.fiber where
  toX := (C.finiteEtale.baseChange S2482AffineOver S2517Point).toSource
  toY := (C.finiteEtale.baseChange S2482AffineOver S2517Point).projectionMap.transformation
  xToBase := C.map
  yToBase := S2517Point
  commutes := (C.finiteEtale.baseChange S2482AffineOver S2517Point).commutes

/-- The witness of the base-change square. -/
noncomputable def S2517Witness (C : S2517Cover) :
    (S2517Square C).TwoPullbackWitness :=
  (C.finiteEtale.baseChange S2482AffineOver S2517Point).isPullback

/-- The cone over the target cover's base-change square induced by a cover map. -/
noncomputable def S2517Cone {C D : S2517Cover}
    (φ : OrbicurveFiniteEtaleCoverMap C D) :
    (S2517Square D).Cone (S2517YS (C.finiteEtale.baseChange S2482AffineOver S2517Point).pullbackScheme) where
  toX := Pseudofunctor.StrongTrans.vcomp
    (C.finiteEtale.baseChange S2482AffineOver S2517Point).toSource φ.map
  toY := (C.finiteEtale.baseChange S2482AffineOver S2517Point).projectionMap.transformation
  commutes := by
    let bcC := C.finiteEtale.baseChange S2482AffineOver S2517Point
    let Bicat := EtaleStackPseudofunctor F
    letI : Bicategory Bicat := inferInstance
    let W : Bicat := S2517YS bcC.pullbackScheme
    let A : Bicat := C.source.fiber
    let B : Bicat := D.source.fiber
    let Z : Bicat := S2482Orbicurve.stack.fiber
    let f : W ⟶ A := bcC.toSource
    let g : A ⟶ B := φ.map
    let h : B ⟶ Z := D.map
    let h' : A ⟶ Z := C.map
    let e1 : Iso (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp f g) h)
        (Pseudofunctor.StrongTrans.vcomp f
          (Pseudofunctor.StrongTrans.vcomp g h)) :=
      @Bicategory.associator Bicat _ W A B Z f g h
    let e2 : Iso (Pseudofunctor.StrongTrans.vcomp f
          (Pseudofunctor.StrongTrans.vcomp g h))
        (Pseudofunctor.StrongTrans.vcomp f h') :=
      @Bicategory.whiskerLeftIso Bicat _ W A Z f
        (Pseudofunctor.StrongTrans.vcomp g h) h' φ.commutes
    let e3 : Iso (Pseudofunctor.StrongTrans.vcomp f h')
        (Pseudofunctor.StrongTrans.vcomp bcC.projectionMap.transformation S2517Point) :=
      bcC.commutes
    exact e1.trans (e2.trans e3)

/-- The underlying scheme morphism of the map of base-change covers. -/
noncomputable def S2517MapHom {C D : S2517Cover}
    (φ : OrbicurveFiniteEtaleCoverMap C D) :
    (C.finiteEtale.baseChange S2482AffineOver S2517Point).pullbackScheme ⟶
      (D.finiteEtale.baseChange S2482AffineOver S2517Point).pullbackScheme :=
  S1742HomOfStrongTrans ((S2517Witness D).lift _ (S2517Cone φ))

theorem S2517MapHom_projection {C D : S2517Cover}
    (φ : OrbicurveFiniteEtaleCoverMap C D) :
    (S2517MapHom φ).left ≫
        (D.finiteEtale.baseChange S2482AffineOver S2517Point).projection.left =
      (C.finiteEtale.baseChange S2482AffineOver S2517Point).projection.left := by
  let bcC := C.finiteEtale.baseChange S2482AffineOver S2517Point
  let bcD := D.finiteEtale.baseChange S2482AffineOver S2517Point
  let cone := S2517Cone φ
  let lift := (S2517Witness D).lift (S2517YS bcC.pullbackScheme) cone
  have hIso := (S2517Witness D).liftToY (S2517YS bcC.pullbackScheme) cone
  have hEq : S1742HomOfStrongTrans
        (Pseudofunctor.StrongTrans.vcomp lift (S2517Square D).toY) =
      S1742HomOfStrongTrans cone.toY :=
    S1742HomOfStrongTrans_congr hIso
  have hleft := congrArg (fun L => L.left) hEq
  rw [S1742HomOfStrongTrans_vcomp] at hleft
  have hDtrans : bcD.projectionMap.transformation =
      S1742StrongTransOfHom bcD.projection := by
    apply S1761StrongTrans_ext (S := bcD.pullbackScheme) (T := S2482AffineOver)
    intro U
    rw [bcD.projectionMap.app_eq U.as]
    rfl
  have hD :
      (S1742HomOfStrongTrans bcD.projectionMap.transformation).left =
        bcD.projection.left := by
    rw [hDtrans, S1742HomOfStrongTrans_strongTransOfHom]
  have hCtrans : cone.toY = S1742StrongTransOfHom bcC.projection := by
    apply S1761StrongTrans_ext (S := bcC.pullbackScheme) (T := S2482AffineOver)
    intro U
    change bcC.projectionMap.transformation.app U =
      (S1742StrongTransOfHom bcC.projection).app U
    rw [bcC.projectionMap.app_eq U.as]
    rfl
  have hC :
      (S1742HomOfStrongTrans cone.toY).left = bcC.projection.left := by
    rw [hCtrans, S1742HomOfStrongTrans_strongTransOfHom]
  have hDsq :
      (S1742HomOfStrongTrans (S2517Square D).toY).left =
        bcD.projection.left := by
    change (S1742HomOfStrongTrans bcD.projectionMap.transformation).left =
      bcD.projection.left
    exact hD
  simpa [S2517MapHom, bcC, bcD, cone, lift, hD, hC, hDsq, Over.Hom.left] using hleft

noncomputable def S2517Map {C D : S2517Cover}
    (φ : OrbicurveFiniteEtaleCoverMap C D) :
    S2517Obj C ⟶ S2517Obj D :=
  ObjectProperty.homMk (Over.homMk (S2517MapHom φ).left
    (S2517MapHom_projection φ))

#check S2517Map
#print axioms S2517Map

end LeanFormal.IUT.XiFPaper.S2517CoverEquivMapActual
end
