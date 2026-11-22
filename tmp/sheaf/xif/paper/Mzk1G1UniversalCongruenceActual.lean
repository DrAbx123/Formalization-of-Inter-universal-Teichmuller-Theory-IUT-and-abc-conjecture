/- Route 7.2 step 5, coefficient congruence: the residue monic polynomial built from the
mod p^N reduction of an integral monic polynomial differs from it by coefficients divisible
by p^N, hence the coefficient distance is at most p^{-N} (strictly below p^{-(N-1)}). -/
import tmp.sheaf.xif.paper.Mzk1G1UniversalResiduePolysActual
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1UniversalCongruenceActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalResiduePolysActual

variable {p : Nat} [Fact p.Prime]

/-- The canonical lift of the residue class of x modulo p^N is congruent to x modulo p^N. -/
theorem residueCoeffLift_toZModPow_sub_mem (N : Nat) (x : ℤ_[p]) :
    residueCoeffLift p N (PadicInt.toZModPow N x) - x ∈
      (Ideal.span {(p : ℤ_[p]) ^ N} : Ideal ℤ_[p]) := by
  have hmap : (PadicInt.toZModPow N) (residueCoeffLift p N (PadicInt.toZModPow N x)) =
      PadicInt.toZModPow N x := by
    simp only [residueCoeffLift, map_natCast]
    rw [ZMod.natCast_zmod_val]
  have hmem : x - residueCoeffLift p N (PadicInt.toZModPow N x) ∈
      RingHom.ker (PadicInt.toZModPow N : ℤ_[p] →+* ZMod (p ^ N)) := by
    rw [RingHom.mem_ker, map_sub, hmap, sub_self]
  have hspan : x - residueCoeffLift p N (PadicInt.toZModPow N x) ∈
      (Ideal.span {(p : ℤ_[p]) ^ N} : Ideal ℤ_[p]) := by
    rwa [PadicInt.ker_toZModPow] at hmem
  rw [← neg_sub x (residueCoeffLift p N (PadicInt.toZModPow N x))]
  exact neg_mem hspan

/-- Coefficient congruence of the residue monic polynomial: the difference in every degree is
divisible by p^N. -/
theorem residueMonicPoly_coeff_sub_mem (N d : Nat) (f : Polynomial ℤ_[p]) (hf : f.Monic)
    (hdeg : f.natDegree = d) (i : Nat) :
    (residueMonicPoly p N d (fun j => PadicInt.toZModPow N (f.coeff j))).coeff i - f.coeff i ∈
      (Ideal.span {(p : ℤ_[p]) ^ N} : Ideal ℤ_[p]) := by
  by_cases hi : i < d
  · rw [@residueMonicPoly_coeff_of_lt p _ N d
      (fun j => PadicInt.toZModPow N (f.coeff j)) i hi]
    exact residueCoeffLift_toZModPow_sub_mem N (f.coeff i)
  · by_cases hid : i = d
    · rw [hid]
      rw [@residueMonicPoly_coeff_self p _ N d
        (fun j => PadicInt.toZModPow N (f.coeff j)), ← hdeg, hf.coeff_natDegree, sub_self]
      exact Ideal.zero_mem _
    · have hgt : d < i := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hi) (Ne.symm hid)
      rw [@residueMonicPoly_coeff_of_gt p _ N d
        (fun j => PadicInt.toZModPow N (f.coeff j)) i hgt,
        coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hgt), sub_zero]
      exact Ideal.zero_mem _

/-- Norm form: all coefficients of the residue monic polynomial are closer than p^{-(N-1)} to
the corresponding coefficients of f. -/
theorem residueMonicPoly_coeff_close (N d : Nat) (hN : 0 < N) (f : Polynomial ℤ_[p])
    (hf : f.Monic) (hdeg : f.natDegree = d) (i : Nat) :
    ‖((residueMonicPoly p N d (fun j => PadicInt.toZModPow N (f.coeff j))).coeff i : ℚ_[p]) -
        (f.coeff i : ℚ_[p])‖ < (p : ℝ) ^ (-(N - 1) : ℤ) := by
  have hmem := residueMonicPoly_coeff_sub_mem N d f hf hdeg i
  have hle : ‖(residueMonicPoly p N d (fun j => PadicInt.toZModPow N (f.coeff j))).coeff i -
      f.coeff i‖ ≤ (p : ℝ) ^ (-(N : ℤ)) :=
    (PadicInt.norm_le_pow_iff_mem_span_pow _ _).mpr hmem
  have hcoe : ((residueMonicPoly p N d (fun j => PadicInt.toZModPow N (f.coeff j))).coeff i : ℚ_[p]) -
      (f.coeff i : ℚ_[p]) =
      (((residueMonicPoly p N d (fun j => PadicInt.toZModPow N (f.coeff j))).coeff i -
        f.coeff i : ℤ_[p]) : ℚ_[p]) := by
    push_cast
    rfl
  rw [hcoe, PadicInt.padic_norm_e_of_padicInt]
  refine lt_of_le_of_lt hle ?_
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlt : (-(N : ℤ)) < -(↑N - 1) := by omega
  exact zpow_lt_zpow_right₀ hp1 hlt

#print axioms residueCoeffLift_toZModPow_sub_mem
#print axioms residueMonicPoly_coeff_sub_mem
#print axioms residueMonicPoly_coeff_close
end LeanFormal.IUT.XiFPaper.Mzk1G1UniversalCongruenceActual
