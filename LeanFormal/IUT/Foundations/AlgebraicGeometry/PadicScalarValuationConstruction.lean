import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure
import Mathlib.NumberTheory.Padics.PadicIntegers

set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

/-!
# Actual p-adic scalar valuation

Constructs the valuation

  `v x = if x = 0 then 0 else exp (-x.valuation)`

on `PadicScalarField place = ℚ_[p]`, proves multiplicativity and the
nonarchimedean inequality from `Padic.valuation_mul` and `Padic.le_valuation_add`,
then builds the `Valued` instance via `Valued.mk'`.

No fake valuation.
-/

noncomputable section

namespace LeanFormal.IUT.PadicScalarValuationConstruction

open scoped WithZero Valued Topology
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

variable {F : Type} [Field F] [NumberField F]
  (place : NumberField.FinitePlace F)

abbrev scalarField (place : NumberField.FinitePlace F) : Type := PadicScalarField place
abbrev completionField (place : NumberField.FinitePlace F) : Type := place.maximalIdeal.adicCompletion F

local instance decScalar : DecidableEq (scalarField place) := Classical.decEq _


noncomputable def padicScalarValuation :
    Valuation (scalarField place) (WithZero (Multiplicative ℤ)) where
  toFun x := if x = 0 then 0 else WithZero.exp (-(x.valuation : ℤ))
  map_zero' := by simp
  map_one' := by
    simp [Padic.valuation_one]
  map_mul' x y := by
    by_cases hx : x = 0
    · subst hx; simp
    · by_cases hy : y = 0
      · subst hy; simp
      · simp only [hx, hy, mul_ne_zero hx hy, ↓reduceIte,
          Padic.valuation_mul hx hy, neg_add, WithZero.exp_add]

  map_add_le_max' x y := by
    by_cases hxy : x + y = 0
    · rw [hxy]; simp
    · by_cases hx : x = 0
      · subst hx; simp
      · by_cases hy : y = 0
        · subst hy; simp
        · simp only [if_neg hxy, if_neg hx, if_neg hy]
          have hmin := Padic.le_valuation_add hxy
          -- negate and exponentiate; the order reverses at the min/max step
          have hneg : -(x + y).valuation ≤ max (-x.valuation) (-y.valuation) :=
          by
            have : min x.valuation y.valuation ≤ (x + y).valuation := hmin
            omega
          have hexp := WithZero.exp_le_exp.mpr hneg
          rcases le_total (-x.valuation : ℤ) (-y.valuation : ℤ) with h | h
          · rw [max_eq_right (WithZero.exp_le_exp.mpr h)]
            exact WithZero.exp_le_exp.mpr (by simpa [max_eq_right h] using hneg)
          · rw [max_eq_left (WithZero.exp_le_exp.mpr h)]
            exact WithZero.exp_le_exp.mpr (by simpa [max_eq_left h] using hneg)

theorem padicScalarValuation_apply (x : scalarField place) :
    padicScalarValuation place x =
      if x = 0 then 0 else WithZero.exp (-(x.valuation : ℤ)) :=
  rfl

theorem padicScalarValuation_of_ne_zero {x : scalarField place} (hx : x ≠ 0) :
    padicScalarValuation place x = WithZero.exp (-(x.valuation : ℤ)) :=
  by simp [padicScalarValuation, hx]

theorem padicScalarValuation_mul (x y : scalarField place) :
    padicScalarValuation place (x * y) =
      padicScalarValuation place x * padicScalarValuation place y :=
  (padicScalarValuation place).map_mul x y

theorem padicScalarValuation_add_le (x y : scalarField place) :
    padicScalarValuation place (x + y) ≤
      max (padicScalarValuation place x) (padicScalarValuation place y) :=
  (padicScalarValuation place).map_add_le_max' x y

noncomputable def padicScalarValued :
    Valued (scalarField place) (WithZero (Multiplicative ℤ)) :=
  Valued.mk' (padicScalarValuation place)

theorem padicScalarValued_v (x : scalarField place) :
    (padicScalarValued place).v x = padicScalarValuation place x :=
  rfl

/-! ## Algebra instance and completion compatibility -/

noncomputable abbrev padicScalarAlgebra :
    Algebra (scalarField place) (completionField place) :=
  padicCompletionAlgebra place

local instance padicScalarAlgebraInstance :
    Algebra (scalarField place) (completionField place) :=
  padicCompletionAlgebra place

theorem padicScalarAlgebra_algebraMap :
    (algebraMap (scalarField place) (completionField place)) =
      padicCompletionHom place :=
  padicCompletionAlgebra_algebraMap place

theorem padicScalarValued_completionCompat (x : scalarField place) :
    Valued.v (algebraMap (scalarField place) (completionField place) x) =
      Valued.v (padicCompletionHom place x) :=
  rfl

end LeanFormal.IUT.PadicScalarValuationConstruction

end