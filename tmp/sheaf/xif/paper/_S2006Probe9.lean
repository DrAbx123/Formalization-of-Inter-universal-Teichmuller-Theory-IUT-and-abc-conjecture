import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.Abel

example {G : Type} [CommGroup G] (a b e ga gb ge : G)
    (hB : gb = (e⁻¹ * (ga / a) * ge) * b) :
    (gb / ga) / (b / a) = e⁻¹ * ge := by
  rw [hB]
  group

example {G : Type} [CommGroup G] (a b e ga gb ge : G)
    (hB : gb = (e⁻¹ * (ga / a) * ge) * b) :
    (gb / ga) / (b / a) = e⁻¹ * ge := by
  rw [hB]
  apply Additive.ofMul.injective
  simp only [div_eq_mul_inv, Additive.ofMul_mul, Additive.ofMul_inv]
  abel

example {G : Type} [CommGroup G] (a b e ga gb ge : G)
    (hB : gb = (e⁻¹ * (ga / a) * ge) * b) :
    (gb / ga) / (b / a) = e⁻¹ * ge := by
  rw [hB]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, inv_mul_rev]
  group

example {G : Type} [CommGroup G] (a b e ga gb ge : G)
    (hB : gb = (e⁻¹ * (ga / a) * ge) * b) :
    (gb / ga) / (b / a) = e⁻¹ * ge := by
  have := congrArg (fun x => (x / ga) / (b / a)) hB
  simp only at this
  rw [← this]
  group
