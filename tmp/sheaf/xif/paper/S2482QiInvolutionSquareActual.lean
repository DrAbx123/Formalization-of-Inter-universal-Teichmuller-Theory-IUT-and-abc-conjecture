import tmp.sheaf.xif.paper.S2482QiInvolutionActual
import tmp.sheaf.xif.paper.S2398HomOfStrongTransCompActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2482QiInvolutionSquareActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2398HomOfStrongTransCompActual
open CategoryTheory

theorem S2482CoordinateRingInvolution_sq :
    S2482CoordinateRingInvolution.comp S2482CoordinateRingInvolution =
      AlgHom.id F S2482CoordinateRing := by
  apply Ideal.Quotient.algHom_ext
  ext x
  fin_cases x <;>
    simp [S2482CoordinateRingInvolution, S2482AffineInvolutionAlgHom,
      Ideal.Quotient.liftₐ]

theorem S2482AffineInvolution_sq :
    S2482AffineInvolution ≫ S2482AffineInvolution = 𝟙 S2482AffineOver := by
  apply Over.OverMorphism.ext
  change AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom S2482CoordinateRingInvolution.toRingHom) ≫
      AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom S2482CoordinateRingInvolution.toRingHom) =
    𝟙 (AlgebraicGeometry.Spec (CommRingCat.of S2482CoordinateRing))
  rw [← AlgebraicGeometry.Spec.map_comp]
  simp only [← CommRingCat.ofHom_comp]
  change AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom
        (↑(S2482CoordinateRingInvolution.comp S2482CoordinateRingInvolution))) =
    𝟙 (AlgebraicGeometry.Spec (CommRingCat.of S2482CoordinateRing))
  rw [S2482CoordinateRingInvolution_sq]
  simpa using AlgebraicGeometry.Spec.map_id
    (CommRingCat.of S2482CoordinateRing)

noncomputable def S2482InducedIdIso :
    Pseudofunctor.StrongTrans.id (S1742YS (F := F) S2482AffineOver) ≅
      S1742StrongTransOfHom (F := F) (𝟙 S2482AffineOver) :=
  Pseudofunctor.StrongTrans.isoMk
    (fun U => eqToIso (by
      apply CategoryTheory.Cat.ext
      apply Discrete.functor_ext
      intro P
      rfl))
    (by
      intro a b g
      apply CategoryTheory.Cat.Hom₂.ext
      apply CategoryTheory.NatTrans.ext
      funext X
      apply ULift.ext
      exact Subsingleton.elim _ _)

theorem S2482EllipticInvolution_comp_underlying :
    S1742HomOfStrongTrans
      (Pseudofunctor.StrongTrans.vcomp
        S2482EllipticInvolution S2482EllipticInvolution) =
      𝟙 S2482AffineOver := by
  change S1742HomOfStrongTrans
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (F := F) S2482AffineInvolution)
        (S1742StrongTransOfHom (F := F) S2482AffineInvolution)) =
    𝟙 S2482AffineOver
  rw [S2398HomOfStrongTrans_vcomp]
  exact S2482AffineInvolution_sq

noncomputable def S2482EllipticInvolution_square :
    Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp
        S2482EllipticInvolution S2482EllipticInvolution)
      (Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve) := by
  let eta := Pseudofunctor.StrongTrans.vcomp
    (S1742StrongTransOfHom (F := F) S2482AffineInvolution)
    (S1742StrongTransOfHom (F := F) S2482AffineInvolution)
  have h : S1742HomOfStrongTrans eta = 𝟙 S2482AffineOver := by
    dsimp [eta]
    rw [S2398HomOfStrongTrans_vcomp]
    exact S2482AffineInvolution_sq
  let e1 : S1742StrongTransOfHom (F := F) (𝟙 S2482AffineOver) ≅ eta := by
    simpa [h] using S1742StrongTransIsoOfHom (F := F) eta
  exact (S2482InducedIdIso.trans e1).symm


end LeanFormal.IUT.XiFPaper.S2482QiInvolutionSquareActual

end