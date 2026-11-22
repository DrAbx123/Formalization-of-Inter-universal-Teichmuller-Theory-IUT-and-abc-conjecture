import tmp.sheaf.xif.paper._P20

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1932SignActionQuotientActual

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1898EllipticInvolutionActual

theorem S1932SignGroup_generator_ne :
    (Multiplicative.ofAdd (1 : ZMod 2) : SignGroup) ≠ 1 := by
  decide

theorem S1932SignGroup_mul_self (x : SignGroup) : x * x = 1 := by
  revert x
  decide

theorem S1932SignGroup_mul_eq_one {x y : SignGroup} (hx : x ≠ 1) (hy : y ≠ 1) :
    x * y = 1 := by
  revert x y
  decide

#print axioms S1932SignGroup_generator_ne
#print axioms S1932SignGroup_mul_self
#print axioms S1932SignGroup_mul_eq_one

end LeanFormal.IUT.XiFPaper.S1932SignActionQuotientActual
end
