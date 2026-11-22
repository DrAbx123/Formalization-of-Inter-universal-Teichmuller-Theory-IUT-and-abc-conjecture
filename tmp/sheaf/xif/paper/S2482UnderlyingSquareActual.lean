import tmp.sheaf.xif.paper.S2482TwoYonedaBridgeActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2482UnderlyingSquareActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open CategoryTheory

variable {S T U : Iut.SchemeOverField F}

abbrev S2482Underlying
    (η : S2482Orbicurve.Hom S2482Orbicurve) :
    S2482AffineOver ⟶ S2482AffineOver :=
  S1742HomOfStrongTrans (F := F) (S := S2482AffineOver) (T := S2482AffineOver)
    (η : Pseudofunctor.StrongTrans
      (S1742YS (F := F) S2482AffineOver)
      (S1742YS (F := F) S2482AffineOver))

theorem S1742HomOfStrongTrans_vcomp
    (η : Pseudofunctor.StrongTrans (S1742YS (F := F) S) (S1742YS (F := F) T))
    (θ : Pseudofunctor.StrongTrans (S1742YS (F := F) T) (S1742YS (F := F) U)) :
    S1742HomOfStrongTrans (Pseudofunctor.StrongTrans.vcomp η θ) =
      S1742HomOfStrongTrans η ≫ S1742HomOfStrongTrans θ := by
  unfold S1742HomOfStrongTrans
  rw [show (Pseudofunctor.StrongTrans.vcomp η θ).app
      (LocallyDiscrete.mk (Opposite.op S)) =
      η.app (LocallyDiscrete.mk (Opposite.op S)) ≫
        θ.app (LocallyDiscrete.mk (Opposite.op S)) from rfl]
  rw [Cat.Hom.comp_obj]
  have h1 : (η.app (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj
      (Discrete.mk (𝟙 S)) = Discrete.mk (S1742HomOfStrongTrans η) := by
    apply Discrete.ext
    exact S1742Key η (LocallyDiscrete.mk (Opposite.op S)) (𝟙 S)
  rw [h1]
  have h2 : (θ.app (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj
      (Discrete.mk (S1742HomOfStrongTrans η)) =
      Discrete.mk (S1742HomOfStrongTrans η ≫ S1742HomOfStrongTrans θ) := by
    apply Discrete.ext
    exact S1742Key θ (LocallyDiscrete.mk (Opposite.op S)) (S1742HomOfStrongTrans η)
  rw [h2]
  rfl


theorem S2482HomOfStrongTrans_comp
    (η : S2482Orbicurve.Hom S2482Orbicurve) :
    S2482Underlying (Iut.HyperbolicOrbicurve.Hom.comp η η) =
      S2482Underlying η ≫ S2482Underlying η := by
  exact S1742HomOfStrongTrans_vcomp
    (η := (η : Pseudofunctor.StrongTrans
      (S1742YS (F := F) S2482AffineOver)
      (S1742YS (F := F) S2482AffineOver)))
    (θ := (η : Pseudofunctor.StrongTrans
      (S1742YS (F := F) S2482AffineOver)
      (S1742YS (F := F) S2482AffineOver)))

theorem S2482HomOfStrongTrans_square_of_iso
    (η : S2482Orbicurve.Hom S2482Orbicurve)
    (hη : Nonempty (Iso
      (Iut.HyperbolicOrbicurve.Hom.comp η η)
      (Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve))) :
    S2482Underlying η ≫ S2482Underlying η =
      𝟙 S2482AffineOver := by
  rcases hη with ⟨e⟩
  have h := S1742HomOfStrongTrans_congr e
  change S2482Underlying (Iut.HyperbolicOrbicurve.Hom.comp η η) =
    S2482Underlying (Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve) at h
  rw [S2482HomOfStrongTrans_comp] at h
  have hid : (((Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve).app
      (LocallyDiscrete.mk (Opposite.op S2482AffineOver))).toFunctor.obj
      (Discrete.mk (𝟙 S2482AffineOver))).as = 𝟙 S2482AffineOver := rfl
  have hid' : S2482Underlying (Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve) =
      𝟙 S2482AffineOver := by
    simpa [S2482Underlying, S1742HomOfStrongTrans] using hid
  rw [hid'] at h
  exact h


end LeanFormal.IUT.XiFPaper.S2482UnderlyingSquareActual
end