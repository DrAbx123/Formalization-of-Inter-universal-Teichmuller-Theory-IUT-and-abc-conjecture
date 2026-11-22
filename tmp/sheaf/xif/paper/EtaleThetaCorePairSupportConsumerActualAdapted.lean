import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoreCoeffAtPairSymmetryActual
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtPairSymmetryActual
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCorePairSupportConsumerActualAdapted

universe u

theorem thetaCoeffAt_support_consumer (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).support ⊆ ({thetaUExponent n, thetaUExponent (-n - 1)} : Set Int) := by
  unfold thetaCoeffAt thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_single]
  simp only [if_pos rfl]
  intro x hx
  rcases HahnSeries.support_add_subset _ _ hx with h | h
  · left; exact HahnSeries.support_single_subset h
  · right; exact HahnSeries.support_single_subset h

#check thetaCoeffAt_support_consumer

end LeanFormal.IUT.XiFPaper.EtaleThetaCorePairSupportConsumerActualAdapted
