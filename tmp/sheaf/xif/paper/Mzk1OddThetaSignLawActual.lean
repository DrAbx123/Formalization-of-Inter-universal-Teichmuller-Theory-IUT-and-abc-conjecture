import LeanFormal.IUT.Foundations.Theta.OddTheta
import LeanFormal.IUT.Foundations.Theta.OddThetaTermAlgebra

/-!
# Mzk1OddThetaSignLawActual — derived sign laws for the odd theta series (new theorems)

Derived from the existing tree odd-theta assets (oddThetaSign def, oddThetaSign_sq,
oddThetaSign_add, oddThetaSign_eq_pow). Genuine new theorems, no copies/bookkeeping.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1OddThetaSignLawActual

open LeanFormal.IUT.Foundations.Theta

universe u

variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- The odd theta sign is invariant under negation of the index. -/
theorem oddThetaSign_neg' (a : ℤ) :
    oddThetaSign (L := L) (-a) = oddThetaSign (L := L) a := by
  have h1 : oddThetaSign (L := L) (-a) * oddThetaSign (L := L) a = 1 := by
    rw [← oddThetaSign_add]
    simp
  have h2 : oddThetaSign (L := L) a * oddThetaSign (L := L) a = 1 :=
    oddThetaSign_sq a
  calc oddThetaSign (L := L) (-a)
      = oddThetaSign (L := L) (-a) * 1 := (mul_one _).symm
    _ = oddThetaSign (L := L) (-a) *
          (oddThetaSign (L := L) a * oddThetaSign (L := L) a) := by rw [h2]
    _ = (oddThetaSign (L := L) (-a) * oddThetaSign (L := L) a) *
          oddThetaSign (L := L) a := by ring
    _ = 1 * oddThetaSign (L := L) a := by rw [h1]
    _ = oddThetaSign (L := L) a := one_mul _

/-- The odd theta sign is a square root of unity, so it is 1 or -1. -/
theorem oddThetaSign_eq_one_or_neg_one (a : ℤ) :
    oddThetaSign (L := L) a = 1 ∨ oddThetaSign (L := L) a = -1 := by
  have hsq : oddThetaSign (L := L) a * oddThetaSign (L := L) a = 1 :=
    oddThetaSign_sq a
  have hfac : (oddThetaSign (L := L) a - 1) * (oddThetaSign (L := L) a + 1) = 0 := by
    have hid : (oddThetaSign (L := L) a - 1) * (oddThetaSign (L := L) a + 1)
        = oddThetaSign (L := L) a * oddThetaSign (L := L) a - 1 := by ring
    rw [hid, hsq]
    ring
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_iff_add_eq_zero.mpr h)

/-- The odd theta sign is nonzero. -/
theorem oddThetaSign_ne_zero' (a : ℤ) : oddThetaSign (L := L) a ≠ 0 := by
  intro h
  have hsq : oddThetaSign (L := L) a * oddThetaSign (L := L) a = 1 :=
    oddThetaSign_sq a
  rw [h, mul_zero] at hsq
  exact zero_ne_one hsq

/-- Sign of zero is one. -/
theorem oddThetaSign_zero' : oddThetaSign (L := L) 0 = 1 := by
  rw [oddThetaSign_eq_pow]
  simp

/-- The sign of a difference is the product of signs. -/
theorem oddThetaSign_sub (m n : ℤ) :
    oddThetaSign (L := L) (m - n) = oddThetaSign (L := L) m * oddThetaSign (L := L) n := by
  rw [sub_eq_add_neg, oddThetaSign_add, oddThetaSign_neg']

#check oddThetaSign_neg'
#check oddThetaSign_eq_one_or_neg_one
#check oddThetaSign_ne_zero'
#check oddThetaSign_zero'
#check oddThetaSign_sub

end LeanFormal.IUT.XiFPaper.Mzk1OddThetaSignLawActual
end
