import LeanFormal.IUT.IUTII.Frobenioid.ConcreteSourceFrobenioidBridge
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalInputs

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-!
# DVR decomposition for the actual completed valuation (L0.4 A/C)

Scratch.  Let `K` be the actual completed valuation at `concretePlace.maximalIdeal`
and `π` the actual production uniformizer `adicCompletion_uniformizer`, with
`Valued.v π = WithZero.exp (-1)`.  For every unit `u : Kˣ` we prove the DVR
decomposition

  `u = π^m * u0`,  `m : ℤ`,  `u0 : (Valued.v.integer)ˣ`,

where `u0` is an actual integral unit obtained from the valuation.  This is the
unit part of the missing log-normalization input.  The refinement `u0` principal
(or `u0^N` principal for an explicit torsion boundary) is **not** claimed here:
the production principal-unit theorem is stated for the normalized norm, while
the present decomposition uses the actual valuation integers; the comparison of
the two unit balls is the separate normalized-norm formula.  No wrapper inhabitant
of `LogExtensionNormalizationCard` is constructed.
-/

noncomputable section

namespace LeanFormal.IUT.UniformizerDVRDecomposition

open scoped WithZero Valued
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge

universe u

local instance gaussianDVRDecompositionIrreducibleFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨LeanFormal.IUT.gaussianPolynomial_irreducible⟩

/-- The actual completed valuation field at the concrete Gaussian place. -/
abbrev completionField : Type :=
  concretePlace.maximalIdeal.adicCompletion GaussianField

/-- The actual production uniformizer of the completed valuation. -/
noncomputable def concreteAdicUniformizer : completionField :=
  ((LeanFormal.IUT.NumberFieldFinitePlace.adicCompletion_uniformizer
      (K := GaussianField) concretePlace.maximalIdeal).1 : completionField)

theorem concreteAdicUniformizer_valued :
    (Valued.v (concreteAdicUniformizer) : WithZero (Multiplicative ℤ)) =
      WithZero.exp (-1 : ℤ) := by
  simpa [concreteAdicUniformizer] using
    LeanFormal.IUT.NumberFieldFinitePlace.uniformizer_valued_eq_exp_neg_one
      (K := GaussianField) (v := concretePlace.maximalIdeal)
      (LeanFormal.IUT.NumberFieldFinitePlace.adicCompletion_uniformizer
        (K := GaussianField) concretePlace.maximalIdeal)

theorem concreteAdicUniformizer_ne_zero : concreteAdicUniformizer ≠ 0 := by
  have h := (LeanFormal.IUT.NumberFieldFinitePlace.adicCompletion_uniformizer
    (K := GaussianField) concretePlace.maximalIdeal).ne_zero
  simpa [concreteAdicUniformizer] using h

/-! ## The value of a unit -/

theorem unit_valued_ne_zero (u : completionFieldˣ) :
    (Valued.v (u : completionField) : WithZero (Multiplicative ℤ)) ≠ 0 :=
  fun h => Units.ne_zero u ((Valued.v).map_eq_zero_iff.mp h)

/-- The integer `m` such that `Valued.v u = exp m`. -/
noncomputable def unitValuationExponent (u : completionFieldˣ) : ℤ :=
  WithZero.log (Valued.v (u : completionField))

theorem unit_valued_eq_exp (u : completionFieldˣ) :
    (Valued.v (u : completionField) : WithZero (Multiplicative ℤ)) =
      WithZero.exp (unitValuationExponent u) := by
  dsimp [unitValuationExponent]
  exact (WithZero.exp_log (unit_valued_ne_zero u)).symm

theorem uniformizer_pow_valued (m : ℤ) :
    (Valued.v (concreteAdicUniformizer ^ m) :
        WithZero (Multiplicative ℤ)) =
      WithZero.exp (-m) := by
  rw [map_zpow₀, concreteAdicUniformizer_valued]
  rw [show WithZero.exp (-1 : ℤ) ^ m = WithZero.exp (m • (-1 : ℤ)) from
    (WithZero.exp_zsmul m (-1 : ℤ)).symm]
  congr 1
  simp

/-- **DVR unit decomposition.** Every unit of the actual completion is
`π^m` times an actual integral unit `u0 : (Valued.v.integer)ˣ`. -/
theorem exists_uniformizer_dvr_decomposition (u : completionFieldˣ) :
    ∃ m : ℤ, ∃ u0 : (Valued.v.integer)ˣ,
      (u : completionField) = concreteAdicUniformizer ^ m *
        ((u0.val).1 : completionField) :=
by
  let k : ℤ := unitValuationExponent u
  let x : completionField := (u : completionField) * concreteAdicUniformizer ^ k
  have hxval : (Valued.v x : WithZero (Multiplicative ℤ)) = 1 := by
    dsimp [x]
    rw [map_mul, unit_valued_eq_exp, uniformizer_pow_valued]
    rw [← WithZero.exp_add]
    rw [show k + -k = 0 by ring, WithZero.exp_zero]
  have hxmem : x ∈ Valued.v.integer := by
    rw [Valuation.mem_integer_iff]
    exact le_of_eq hxval
  have hx0 : x ≠ 0 :=
    mul_ne_zero (Units.ne_zero u) (zpow_ne_zero k concreteAdicUniformizer_ne_zero)
  have hxinvval : (Valued.v x⁻¹ : WithZero (Multiplicative ℤ)) = 1 := by
    rw [map_inv₀, hxval, inv_one]
  have hxinvmem : x⁻¹ ∈ Valued.v.integer := by
    rw [Valuation.mem_integer_iff]
    exact le_of_eq hxinvval
  let u0 : (Valued.v.integer)ˣ :=
    { val := ⟨x, hxmem⟩
      inv := ⟨x⁻¹, hxinvmem⟩
      val_inv := by
        apply Subtype.ext
        change x * x⁻¹ = 1
        exact mul_inv_cancel₀ hx0
      inv_val := by
        apply Subtype.ext
        change x⁻¹ * x = 1
        exact inv_mul_cancel₀ hx0 }
  refine ⟨-k, u0, ?_⟩
  change (u : completionField) =
    concreteAdicUniformizer ^ (-k) * ((u0.val).1 : completionField)
  rw [show ((u0.val).1 : completionField) = x from rfl]
  dsimp [x]
  rw [zpow_neg,
    mul_comm ((concreteAdicUniformizer ^ k)⁻¹)
      ((u : completionField) * concreteAdicUniformizer ^ k),
    mul_assoc,
    mul_inv_cancel₀ (zpow_ne_zero k concreteAdicUniformizer_ne_zero),
    mul_one]
end LeanFormal.IUT.UniformizerDVRDecomposition

end