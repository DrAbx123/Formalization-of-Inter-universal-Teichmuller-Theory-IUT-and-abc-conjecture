import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtSupportFiniteActualAdapted

universe u

noncomputable def thetaTermEx (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  HahnSeries.single (thetaQExponent n)
    (HahnSeries.single (thetaUExponent n) ((-1 : K) ^ n))

noncomputable def thetaPairTerm (K : Type u) [Field K] (n : Int) :
    HahnSeries HalfInt (HahnSeries Int K) :=
  thetaTermEx K n + thetaTermEx K (-n - 1)

noncomputable def thetaCoeffAt (K : Type u) [Field K] (n : Int) :
    HahnSeries Int K :=
  (thetaPairTerm K n).coeff (thetaQExponent n)

theorem thetaCoeffAt_support (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).support ⊆ ({thetaUExponent n, thetaUExponent (-n - 1)} : Set Int) := by
  unfold thetaCoeffAt thetaPairTerm thetaTermEx
  rw [thetaQExponent_neg_succ]
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_single]
  simp only [if_pos rfl]
  intro x hx
  rcases HahnSeries.support_add_subset _ _ hx with h | h
  · left; exact HahnSeries.support_single_subset h
  · right; exact HahnSeries.support_single_subset h

theorem thetaCoeffAt_support_finite (K : Type u) [Field K] (n : Int) :
    (thetaCoeffAt K n).support.Finite := by
  refine Set.Finite.subset ?_ (thetaCoeffAt_support K n)
  exact (Set.finite_singleton (thetaUExponent (-n - 1))).insert (thetaUExponent n)

#check thetaCoeffAt_support_finite

end LeanFormal.IUT.XiFPaper.EtaleThetaCoreCoeffAtSupportFiniteActualAdapted
