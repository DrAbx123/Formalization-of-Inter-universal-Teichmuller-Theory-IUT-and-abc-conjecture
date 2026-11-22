import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import tmp.sheaf.xif.paper.S1667AdmissibleCurveActual
import Mathlib.Tactic

noncomputable section
open WeierstrassCurve
open Polynomial

namespace Probe6

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

abbrev K5 := ℚ_[5]
abbrev R5 := ℤ_[5]

lemma norm_61_64 : ‖(61/64 : K5)‖ = 1 := by
  rw [show (61/64 : K5) = ((61:ℕ):K5) / ((64:ℕ):K5) by norm_num]
  rw [norm_div]
  have h1 : ‖((61:ℕ) : K5)‖ = 1 := (Padic.norm_natCast_eq_one_iff (p := 5) (n := 61)).2 (by norm_num)
  have h2 : ‖((64:ℕ) : K5)‖ = 1 := (Padic.norm_natCast_eq_one_iff (p := 5) (n := 64)).2 (by norm_num)
  rw [h1, h2]
  norm_num

lemma norm_neg125_64 : ‖(-125/64 : K5)‖ = 1 := by
  rw [show (-125/64 : K5) = ((-125:ℤ):K5) / ((64:ℕ):K5) by norm_num]
  rw [norm_div]
  have h1 : ‖((-125:ℤ) : K5)‖ = 1 := (Padic.norm_intCast_eq_one_iff (p := 5) (z := -125)).2 (by norm_num)
  have h2 : ‖((64:ℕ) : K5)‖ = 1 := (Padic.norm_natCast_eq_one_iff (p := 5) (n := 64)).2 (by norm_num)
  rw [h1, h2]
  norm_num

def z2 : R5 := (PadicInt.mkUnits (p := 5) norm_61_64 : R5)
def z4 : R5 := (PadicInt.mkUnits (p := 5) norm_neg125_64 : R5)

example : ((z2 : R5) : K5) = 61/64 := by
  rw [z2, PadicInt.mkUnits_eq]

example : ((z4 : R5) : K5) = -125/64 := by
  rw [z4, PadicInt.mkUnits_eq]

example : z2 * (64 : R5) = (61 : R5) := by
  ext
  rw [z2, PadicInt.mkUnits_eq]
  push_cast
  norm_num

example : z4 * (64 : R5) = (-125 : R5) := by
  ext
  rw [z4, PadicInt.mkUnits_eq]
  push_cast
  norm_num

example : PadicInt.toZMod z2 = 4 := by
  have hz : PadicInt.toZMod z2 * (4 : ZMod 5) = 1 := by
    have h := congrArg (PadicInt.toZMod (p := 5)) (show z2 * (64 : R5) = (61 : R5) from by
      ext
      rw [z2, PadicInt.mkUnits_eq]
      push_cast
      norm_num)
    norm_num at h
    simpa using h
  calc PadicInt.toZMod z2 = PadicInt.toZMod z2 * 1 := by ring
    _ = PadicInt.toZMod z2 * ((4 : ZMod 5) * 4) := by norm_num
    _ = (PadicInt.toZMod z2 * 4) * 4 := by ring
    _ = 1 * 4 := by rw [hz]
    _ = 4 := by norm_num

example : PadicInt.toZMod z4 = 0 := by
  have hz : PadicInt.toZMod z4 * (4 : ZMod 5) = 0 := by
    have h := congrArg (PadicInt.toZMod (p := 5)) (show z4 * (64 : R5) = (-125 : R5) from by
      ext
      rw [z4, PadicInt.mkUnits_eq]
      push_cast
      norm_num)
    norm_num at h
    simpa using h
  calc PadicInt.toZMod z4 = PadicInt.toZMod z4 * 1 := by ring
    _ = PadicInt.toZMod z4 * ((4 : ZMod 5) * 4) := by norm_num
    _ = (PadicInt.toZMod z4 * 4) * 4 := by ring
    _ = 0 * 4 := by rw [hz]
    _ = 0 := by norm_num

def I0 : WeierstrassCurve R5 := WeierstrassCurve.mk 0 z2 0 z4 0

example : I0.map (algebraMap R5 K5) = S1667Curve.baseChange K5 := by
  ext <;> simp [I0, z2, z4, S1667Curve, WeierstrassCurve.baseChange]
  · rw [PadicInt.mkUnits_eq]
  · rw [PadicInt.mkUnits_eq]
  · -- a4
    rw [PadicInt.mkUnits_eq]
    norm_num
  · -- a6 maybe
    norm_num

end Probe6
