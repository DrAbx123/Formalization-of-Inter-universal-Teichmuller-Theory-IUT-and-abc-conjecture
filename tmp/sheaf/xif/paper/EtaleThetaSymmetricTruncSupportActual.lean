import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSupportActual

universe u

noncomputable def thetaTermEx (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  HahnSeries.single (thetaQExponent n)
    (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n))

noncomputable def thetaPairTerm (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  thetaTermEx K n + thetaTermEx K (-n - 1)

theorem thetaPairTerm_support (K : Type u) [Field K] (n : Int) :
    (thetaPairTerm K n).support ⊆ ({thetaQExponent n} : Set HalfInt) := by
  unfold thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  intro x hx
  rcases HahnSeries.support_add_subset _ _ hx with h | h
  · exact Set.mem_singleton_iff.mpr (HahnSeries.support_single_subset h)
  · exact Set.mem_singleton_iff.mpr (HahnSeries.support_single_subset h)

#check thetaPairTerm_support

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncSupportActual
