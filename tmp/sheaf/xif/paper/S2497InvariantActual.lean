import tmp.sheaf.xif.paper.S2497FixednessActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiCurveActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2495cFUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2496cFMapActual
open LeanFormal.IUT.XiFPaper.S2497FixednessActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2497InvariantActual

theorem S2497PhiInv :
    S2482CoordinateRingInvolution.toRingHom.comp S2496phi = S2496phi := by
  apply MvPolynomial.ringHom_ext
  · intro a
    have h : S2496phi (MvPolynomial.C a) = algebraMap F S2482CoordinateRing a := by
      rw [S2496phi, MvPolynomial.eval₂Hom_C]
    change S2482CoordinateRingInvolution (S2496phi (MvPolynomial.C a)) =
      S2496phi (MvPolynomial.C a)
    rw [h]
    exact S2497_fixed_const a
  · intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    have h : S2496phi (MvPolynomial.X (0 : Fin 1)) =
        Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) (MvPolynomial.X 0) := by
      rw [S2496phi, MvPolynomial.eval₂Hom_X']
    change S2482CoordinateRingInvolution (S2496phi (MvPolynomial.X 0)) =
      S2496phi (MvPolynomial.X 0)
    rw [h]
    exact S2497_fixed_X0

theorem S2497InvScheme :
    S2482AffineInvolution ≫ S2496f = S2496f := by
  apply CategoryTheory.Over.OverMorphism.ext
  dsimp [S2482AffineInvolution, S2496f]
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
      (S2482CoordinateRingInvolution.toRingHom.comp S2496phi)) =
    Spec.map (CommRingCat.ofHom S2496phi)
  rw [S2497PhiInv]

#print axioms S2497PhiInv
#print axioms S2497InvScheme

end LeanFormal.IUT.XiFPaper.S2497InvariantActual
end