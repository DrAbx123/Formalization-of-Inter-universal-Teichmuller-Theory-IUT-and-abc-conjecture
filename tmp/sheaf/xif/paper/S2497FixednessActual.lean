import tmp.sheaf.xif.paper.S2496cFMapActual
import tmp.sheaf.xif.paper.S2482QiInvolutionActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiCurveActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2496cFMapActual
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2497FixednessActual

theorem S2497_fixed_X0 :
    S2482CoordinateRingInvolution
      (Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) (MvPolynomial.X 0)) =
    Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) (MvPolynomial.X 0) := by
  simp [S2482CoordinateRingInvolution, S2482AffineInvolutionAlgHom]

theorem S2497_fixed_const (a : F) :
    S2482CoordinateRingInvolution (algebraMap F S2482CoordinateRing a) =
      algebraMap F S2482CoordinateRing a :=
  S2482CoordinateRingInvolution.commutes a

#print axioms S2497_fixed_X0
#print axioms S2497_fixed_const

end LeanFormal.IUT.XiFPaper.S2497FixednessActual
end