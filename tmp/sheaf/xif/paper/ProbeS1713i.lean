import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import tmp.sheaf.xif.paper.S1667AdmissibleCurveActual
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic

noncomputable section
open WeierstrassCurve
open Polynomial
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT

namespace Probe9

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

abbrev K5 := ℚ_[5]
abbrev R5 := ℤ_[5]

-- Reuse previous definitions quickly
lemma norm_61_64 : ‖(61/64 : K5)‖ = 1 := by
  rw [show (61/64 : K5) = ((61:ℕ):K5) / ((64:ℕ):K5) by norm_num]
  rw [norm_div]
  have h1 : ‖((61:ℕ) : K5)‖ = 1 := (Padic.norm_natCast_eq_one_iff (p := 5) (n := 61)).2 (by norm_num)
  have h2 : ‖((64:ℕ) : K5)‖ = 1 := (Padic.norm_natCast_eq_one_iff (p := 5) (n := 64)).2 (by norm_num)
  rw [h1, h2]; norm_num

lemma norm_neg125_64_lt_one : ‖(-125/64 : K5)‖ < 1 := by
  rw [show (-125/64 : K5) = ((-125:ℤ):K5) / ((64:ℕ):K5) by norm_num]
  rw [norm_div]
  have h1 : ‖((-125:ℤ) : K5)‖ < 1 := by
    rw [Padic.norm_intCast_lt_one_iff]; norm_num
  have h2 : ‖((64:ℕ) : K5)‖ = 1 := (Padic.norm_natCast_eq_one_iff (p := 5) (n := 64)).2 (by norm_num)
  rw [h2, div_one]; exact h1

def z2 : R5 := ⟨(61/64 : K5), le_of_eq norm_61_64⟩
def z4 : R5 := ⟨(-125/64 : K5), le_of_lt norm_neg125_64_lt_one⟩
def I0 : WeierstrassCurve R5 := WeierstrassCurve.mk 0 z2 0 z4 0

theorem z2_mul_64 : z2 * (64 : R5) = (61 : R5) := by
  apply Subtype.ext
  change (61/64 : K5) * (64 : K5) = (61 : K5)
  norm_num

theorem z4_mul_64 : z4 * (64 : R5) = (-125 : R5) := by
  apply Subtype.ext
  change (-125/64 : K5) * (64 : K5) = (-125 : K5)
  norm_num

theorem toZMod_64 : PadicInt.toZMod (64 : R5) = 4 := by
  rw [show (64 : R5) = ((64:ℕ) : R5) by norm_num]
  rw [map_natCast]; decide

theorem toZMod_61 : PadicInt.toZMod (61 : R5) = 1 := by
  rw [show (61 : R5) = ((61:ℕ) : R5) by norm_num]
  rw [map_natCast]; decide

theorem toZMod_neg125 : PadicInt.toZMod (-125 : R5) = 0 := by
  rw [show (-125 : R5) = ((-125:ℤ) : R5) by norm_num]
  rw [map_intCast]; decide

theorem toZMod_z2 : PadicInt.toZMod z2 = 4 := by
  have hz : PadicInt.toZMod z2 * (4 : ZMod 5) = 1 := by
    have h := congrArg (PadicInt.toZMod (p := 5)) z2_mul_64
    rw [map_mul, toZMod_64, toZMod_61] at h
    exact h
  have h4 : ((4 : ZMod 5) * 4) = 1 := by decide
  calc PadicInt.toZMod z2 = PadicInt.toZMod z2 * 1 := by ring
    _ = PadicInt.toZMod z2 * ((4 : ZMod 5) * 4) := by rw [h4]
    _ = (PadicInt.toZMod z2 * 4) * 4 := by ring
    _ = 1 * 4 := by rw [hz]
    _ = 4 := by norm_num

theorem toZMod_z4 : PadicInt.toZMod z4 = 0 := by
  have hz : PadicInt.toZMod z4 * (4 : ZMod 5) = 0 := by
    have h := congrArg (PadicInt.toZMod (p := 5)) z4_mul_64
    rw [map_mul, toZMod_64, toZMod_neg125] at h
    exact h
  have h4 : ((4 : ZMod 5) * 4) = 1 := by decide
  calc PadicInt.toZMod z4 = PadicInt.toZMod z4 * 1 := by ring
    _ = PadicInt.toZMod z4 * ((4 : ZMod 5) * 4) := by rw [h4]
    _ = (PadicInt.toZMod z4 * 4) * 4 := by ring
    _ = 0 * 4 := by rw [hz]
    _ = 0 := by norm_num

theorem I0_baseChange : I0.map (algebraMap R5 K5) = S1667Curve.baseChange K5 := by
  ext <;> simp [I0, z2, z4, S1667Curve, WeierstrassCurve.baseChange]

def J : WeierstrassCurve (ZMod 5) := I0.map (PadicInt.toZMod)

theorem J_eq : J = WeierstrassCurve.mk (0 : ZMod 5) 4 0 0 0 := by
  ext <;> simp [J, I0, toZMod_z2, toZMod_z4]

example : J.c₄ = (1 : ZMod 5) := by
  rw [J_eq]
  decide

example : J.Δ = (0 : ZMod 5) := by
  rw [J_eq]
  decide

example : splitReductionPolynomial J = (X^2 + 1 : (ZMod 5)[X]) := by
  rw [J_eq]
  decide

example : (X^2 + 1 : (ZMod 5)[X]) = (X - C 2) * (X + C 2) := by
  decide

example : (X^2 + 1 : (ZMod 5)[X]).Splits := by
  rw [show (X^2 + 1 : (ZMod 5)[X]) = (X - C 2) * (X + C 2) by decide]
  exact (Polynomial.Splits.X_sub_C 2).mul (Polynomial.Splits.X_add_C 2)

end Probe9
