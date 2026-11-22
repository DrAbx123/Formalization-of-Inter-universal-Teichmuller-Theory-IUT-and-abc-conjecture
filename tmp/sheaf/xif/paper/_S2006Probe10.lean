import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic.Abel

example {G : Type} [CommGroup G] (a b : G) : (a/b)*b = a := by
  have hinj : Function.Injective (Additive.ofMul : G → Additive G) := fun x y h => by
    simpa using congrArg Additive.toMul h
  apply hinj
  simp only [div_eq_mul_inv, ofMul_mul, ofMul_inv]
  abel

example {G : Type} [CommGroup G] (a b e ga gb ge : G)
    (hB : gb = (e⁻¹ * (ga / a) * ge) * b) :
    (gb / ga) / (b / a) = e⁻¹ * ge := by
  have hinj : Function.Injective (Additive.ofMul : G → Additive G) := fun x y h => by
    simpa using congrArg Additive.toMul h
  rw [hB]
  apply hinj
  simp only [div_eq_mul_inv, ofMul_mul, ofMul_inv]
  abel

example {G : Type} [CommGroup G] (x e ge : G) :
    (x * (e⁻¹ * ge)) / ge = x / e := by
  have hinj : Function.Injective (Additive.ofMul : G → Additive G) := fun x y h => by
    simpa using congrArg Additive.toMul h
  apply hinj
  simp only [div_eq_mul_inv, ofMul_mul, ofMul_inv]
  abel

example {G : Type} [CommGroup G] (a b e ga gb ge : G)
    (hB : gb = (e⁻¹ * (ga / a) * ge) * b) :
    (gb / ga) / (b / a) = e⁻¹ * ge := by
  rw [hB]
  apply Additive.ofMul.injective
