import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
open Polynomial NumberField IsCyclotomicExtension
noncomputable section
local instance : NeZero 3 := ⟨by norm_num⟩
local instance : NeZero (3 : ℚ) := ⟨by norm_num⟩
abbrev K := CyclotomicField 3 ℚ
local instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
example : minpoly ℤ (zeta_spec 3 ℚ K).toInteger = (X^2 + X + 1 : ℤ[X]) := by
  let hζ := zeta_spec 3 ℚ K
  let θ := hζ.toInteger
  have hmin : minpoly ℤ θ = (X^2 + X + 1 : ℤ[X]) := by
    rw [← RingOfIntegers.minpoly_coe θ]
    rw [show (↑θ : K) = zeta 3 ℚ K from hζ.coe_toInteger]
    simpa [cyclotomic_three] using (cyclotomic_eq_minpoly hζ (by norm_num)).symm
  exact hmin
