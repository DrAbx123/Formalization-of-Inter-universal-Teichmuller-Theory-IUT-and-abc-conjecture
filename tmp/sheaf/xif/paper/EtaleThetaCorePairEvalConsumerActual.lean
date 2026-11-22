import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoreCoeffAtPairSymmetryActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtPairSymmetryActual
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCorePairEvalConsumerActual

universe u

theorem thetaCoeffAt_coeff_u_consumer (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).coeff (thetaUExponent n) = (-1 : K) ^ n := by
  unfold thetaCoeffAt thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  have hneg : thetaUExponent (-n - 1) = -thetaUExponent n := thetaUExponent_neg_succ n
  rw [hneg]
  have hne : thetaUExponent n ≠ -thetaUExponent n := by
    unfold thetaUExponent; omega
  simp [HahnSeries.coeff_add, HahnSeries.coeff_single, hne]

#check thetaCoeffAt_coeff_u_consumer

end LeanFormal.IUT.XiFPaper.EtaleThetaCorePairEvalConsumerActual
