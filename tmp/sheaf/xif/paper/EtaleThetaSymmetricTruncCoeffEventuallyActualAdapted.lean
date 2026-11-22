import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncSuccActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncCoeffEventuallyActualAdapted

universe u

theorem thetaQExponent_nat_ne_of_lt {N M : Nat} (h : N < M) :
    thetaQExponent (N : Int) ≠ thetaQExponent (M : Int) := by
  unfold thetaQExponent
  have h' : (N : Rat) < (M : Rat) := by exact_mod_cast h
  have hN : (0 : Rat) <= (N : Rat) := by positivity
  nlinarith

theorem etaleThetaSymmetricTrunc_coeff_at_stable (K : Type u) [Field K]
    (M N : Nat) (hN : N <= M) :
    (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc K M).coeff
        (thetaQExponent (N : Int)) =
      (LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc K N).coeff
        (thetaQExponent (N : Int)) := by
  induction M with
  | zero =>
      have hN0 : N = 0 := by omega
      subst N
      rfl
  | succ M ih =>
      by_cases hMN : N = M + 1
      · subst N; rfl
      · have hNM : N <= M := by omega
        rw [LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSuccActual.etaleThetaSymmetricTrunc_coeff_stable K M]
        · exact ih hNM
        · exact thetaQExponent_nat_ne_of_lt (N := N) (M := M + 1) (by omega)

#check etaleThetaSymmetricTrunc_coeff_at_stable

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncCoeffEventuallyActualAdapted
