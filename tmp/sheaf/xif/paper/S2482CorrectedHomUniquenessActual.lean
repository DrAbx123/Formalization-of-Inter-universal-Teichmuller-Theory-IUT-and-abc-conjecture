import tmp.sheaf.xif.paper.S2482SpecPhiActual
import tmp.sheaf.xif.paper.S2482CorrectedUniquenessAlgActual
import tmp.sheaf.xif.paper.S2482TwoYonedaBridgeActual

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2482CorrectedHomUniquenessActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionSquareActual
open LeanFormal.IUT.XiFPaper.S2482SpecPhiActual
open LeanFormal.IUT.XiFPaper.S2482UnderlyingSquareActual
open LeanFormal.IUT.XiFPaper.S2482TwoYonedaBridgeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2482CorrectedUniquenessAlgActual
open LeanFormal.IUT.XiFPaper.S2482OrderTwoAlgAutClassificationAltActual
open CategoryTheory AlgebraicGeometry

noncomputable def S2482PhiRingEquiv
    (η : S2482Orbicurve.Hom S2482Orbicurve)
    (h2 : Nonempty (Iso (Iut.HyperbolicOrbicurve.Hom.comp η η)
      (Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve))) :
    S2482CoordinateRing ≃+* S2482CoordinateRing where
  toFun := S2482Phi η
  invFun := S2482Phi η
  left_inv x := by
    have h := congrArg (fun f : S2482CoordinateRing →+* S2482CoordinateRing =>
      f x) (S2482Phi_comp η h2)
    simpa using h
  right_inv x := by
    have h := congrArg (fun f : S2482CoordinateRing →+* S2482CoordinateRing =>
      f x) (S2482Phi_comp η h2)
    simpa using h
  map_mul' := (S2482Phi η).map_mul
  map_add' := (S2482Phi η).map_add

noncomputable def S2482PhiAlgEquiv
    (η : S2482Orbicurve.Hom S2482Orbicurve)
    (h2 : Nonempty (Iso (Iut.HyperbolicOrbicurve.Hom.comp η η)
      (Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve))) :
    S2482CoordinateRing ≃ₐ[F] S2482CoordinateRing :=
  AlgEquiv.ofRingEquiv (f := S2482PhiRingEquiv η h2)
    (fun r => congrArg (fun f => f r) (S2482Phi_commutes η))

theorem S2482Phi_classification
    (η : S2482Orbicurve.Hom S2482Orbicurve)
    (h2 : Nonempty (Iso (Iut.HyperbolicOrbicurve.Hom.comp η η)
      (Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve))) :
    (S2482PhiAlgEquiv η h2).toAlgHom = AlgHom.id F S2482CoordinateRing ∨
      (S2482PhiAlgEquiv η h2).toAlgHom = S2482CoordinateRingInvolution := by
  apply S2482OrderTwoAlgAutClassification_actual
  apply AlgHom.ext
  intro x
  have h := congrArg (fun f : S2482CoordinateRing →+* S2482CoordinateRing =>
    f x) (S2482Phi_comp η h2)
  simpa [S2482PhiAlgEquiv, S2482PhiRingEquiv] using h


theorem S2482CorrectedHomUniqueness
    (η : S2482Orbicurve.Hom S2482Orbicurve)
    (h2 : Nonempty (Iso (Iut.HyperbolicOrbicurve.Hom.comp η η)
      (Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve)))
    (hnt : ¬ Nonempty (Iso η
      (Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve))) :
    Nonempty (Iso η S2482EllipticInvolution) := by
  rcases S2482Phi_classification η h2 with hid | hsign
  · exfalso
    apply hnt
    have hphi : S2482Phi η = RingHom.id S2482CoordinateRing := by
      have h := congrArg AlgHom.toRingHom hid
      change S2482Phi η = RingHom.id S2482CoordinateRing at h
      exact h
    have hleft : S2482UnderlyingLeft η = 𝟙 S2482AffineScheme := by
      rw [← S2482Phi_spec, hphi]
      change Spec.map (CommRingCat.ofHom (RingHom.id S2482CoordinateRing)) =
        𝟙 S2482AffineScheme
      rw [show CommRingCat.ofHom (RingHom.id S2482CoordinateRing) =
        𝟙 (CommRingCat.of S2482CoordinateRing) from rfl]
      exact Spec.map_id _
    have hg : S2482Underlying η = 𝟙 S2482AffineOver := by
      apply Over.OverMorphism.ext
      change Over.Hom.left (S2482Underlying η) = Over.Hom.left (𝟙 S2482AffineOver)
      rw [← S2482UnderlyingLeft_eq, hleft]
      simp [Over.id_left, S2482AffineOver_left]
    let ηs : Pseudofunctor.StrongTrans
        (S1742YS (F := F) S2482AffineOver)
        (S1742YS (F := F) S2482AffineOver) := η
    have hηs : S1742HomOfStrongTrans ηs = 𝟙 S2482AffineOver := by
      simpa [S2482Underlying] using hg
    have e := S1742StrongTransIsoOfHom (F := F) ηs
    rw [hηs] at e
    have eid : Pseudofunctor.StrongTrans.id
        (S1742YS (F := F) S2482AffineOver) ≅
        S1742StrongTransOfHom (F := F) (𝟙 S2482AffineOver) :=
      S2482InducedIdIso
    exact ⟨e.symm.trans eid.symm⟩
  · have hphi : S2482Phi η = S2482CoordinateRingInvolution.toRingHom := by
      have h := congrArg AlgHom.toRingHom hsign
      change S2482Phi η = S2482CoordinateRingInvolution.toRingHom at h
      exact h
    have hleft : S2482Underlying η = S2482AffineInvolution := by
      apply Over.OverMorphism.ext
      change (S2482Underlying η).left = S2482AffineInvolution.left
      rw [← S2482UnderlyingLeft_eq, ← S2482Phi_spec, hphi]
      rfl
    have hhom : S1742HomOfStrongTrans η = S2482AffineInvolution := by
      simpa [S2482Underlying] using hleft
    exact S2482TwoIso_of_hom_eq η hhom


end LeanFormal.IUT.XiFPaper.S2482CorrectedHomUniquenessActual
end