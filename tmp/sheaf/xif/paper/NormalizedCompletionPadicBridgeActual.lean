import LeanFormal.IUT.ABCBridge.Geometry.RationalCommonPrimeFinrank
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic

/-! # Norm bridge from NormalizedCompletion to its p-adic scalar field

For a rational finite place `P : NumberField.FinitePlace ℚ` the normalized
completion is one-dimensional over its p-adic scalar field, so the algebraic
`algebraMap` is bijective.  The norm on `NormalizedCompletion P` is the
spectral norm, whose restriction to the image of `PadicScalarField P` is the
p-adic norm (`spectralNorm_extends`).  Hence every spectral norm is a p-adic
norm, and principal units inherit the p-adic contraction bound.

No axiom, sorry, True, or fabricated norm equality. -/

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000
open scoped WithZero
open LeanFormal.IUT NumberField MeasureTheory
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits

namespace LeanFormal.IUT.XiFPaper.NormalizedCompletionPadicBridgeActual

variable {P : NumberField.FinitePlace ℚ}

/-- The identity algebra structure on the ring of integers of `ℚ` is the
identity ring hom. -/
theorem ringOfIntegers_algebraMap_self :
    algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers ℚ) =
      RingHom.id (NumberField.RingOfIntegers ℚ) := by
  ext x
  change ((NumberField.RingOfIntegers.mapRingHom (algebraMap ℚ ℚ)) x : ℚ) = (x : ℚ)
  rw [NumberField.RingOfIntegers.mapRingHom_apply]
  simp

/-- A rational finite place is its own contraction. -/
theorem comap_self_rat (P : NumberField.FinitePlace ℚ) :
    comap (k := ℚ) P = P := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NumberFieldFinitePlace.comap_maximalIdeal]
  congr 1

/-- The p-adic scalar algebra map into the normalized completion is bijective
because the completion is one-dimensional over the scalar field. -/
theorem algebraMap_bijective (P : NumberField.FinitePlace ℚ) :
    Function.Bijective (algebraMap (PadicScalarField P) (NormalizedCompletion P)) :=
  (Algebra.finrank_eq_one_iff_bijective_algebraMap).mp
    (finrank_normalizedCompletion_rat P)

/-- The inverse of `algebraMap`, as an equivalence onto the p-adic scalar field. -/
noncomputable def normalizedCompletionPadicEquiv (P : NumberField.FinitePlace ℚ) :
    NormalizedCompletion P ≃ PadicScalarField P :=
  (Equiv.ofBijective (algebraMap (PadicScalarField P) (NormalizedCompletion P))
    (algebraMap_bijective P)).symm

/-- The spectral norm on the algebraic image is the p-adic norm. -/
theorem norm_algebraMap (P : NumberField.FinitePlace ℚ) (c : PadicScalarField P) :
    ‖algebraMap (PadicScalarField P) (NormalizedCompletion P) c‖ = ‖c‖ := by
  change spectralNorm (PadicScalarField P) (NormalizedCompletion P)
    (algebraMap (PadicScalarField P) (NormalizedCompletion P) c) = ‖c‖
  exact spectralNorm_extends (K := PadicScalarField P) (L := NormalizedCompletion P) c

/-- Every element of the normalized completion has spectral norm equal to the
p-adic norm of its scalar coordinate. -/
theorem norm_eq_padic (P : NumberField.FinitePlace ℚ) (x : NormalizedCompletion P) :
    ‖x‖ = ‖normalizedCompletionPadicEquiv P x‖ := by
  have hx : algebraMap (PadicScalarField P) (NormalizedCompletion P)
      (normalizedCompletionPadicEquiv P x) = x := by
    let e : PadicScalarField P ≃ NormalizedCompletion P :=
      Equiv.ofBijective _ (algebraMap_bijective P)
    have hsym : normalizedCompletionPadicEquiv P x = e.symm x := rfl
    rw [hsym]
    exact Equiv.apply_symm_apply e x
  calc ‖x‖ = ‖algebraMap (PadicScalarField P) (NormalizedCompletion P)
        (normalizedCompletionPadicEquiv P x)‖ := by rw [hx]
    _ = ‖normalizedCompletionPadicEquiv P x‖ := norm_algebraMap P _

/-- In particular the identity has norm one for the spectral norm. -/
theorem norm_one_normalizedCompletion (P : NumberField.FinitePlace ℚ) :
    ‖(1 : NormalizedCompletion P)‖ = 1 := by
  have hmap : normalizedCompletionPadicEquiv P (1 : NormalizedCompletion P) = 1 := by
    let e : PadicScalarField P ≃ NormalizedCompletion P :=
      Equiv.ofBijective _ (algebraMap_bijective P)
    have hsym : normalizedCompletionPadicEquiv P (1 : NormalizedCompletion P) = e.symm 1 := rfl
    rw [hsym]
    apply e.injective
    rw [Equiv.apply_symm_apply]
    exact (map_one (algebraMap (PadicScalarField P) (NormalizedCompletion P))).symm
  rw [norm_eq_padic P 1, hmap]
  exact norm_one

/-- The spectral-norm field is a `NormOneClass` (the generic instance supplies
it; the proof is recorded explicitly through the spectral norm). -/
theorem norm_one_class_normalizedCompletion (P : NumberField.FinitePlace ℚ) :
    NormOneClass (NormalizedCompletion P) :=
  ⟨norm_one_normalizedCompletion P⟩

/-- A principal unit of the normalized completion has spectral norm `< 1`. -/
theorem principal_unit_norm_lt_one (P : NumberField.FinitePlace ℚ)
    (x : (Integers (NormalizedCompletion P))ˣ)
    (hx : x ∈ principalUnits (K := NormalizedCompletion P)) :
    ‖(((x.val : Integers (NormalizedCompletion P)) : NormalizedCompletion P) - 1)‖ < 1 :=
  (mem_principalUnits_iff _).mp hx

/-- Principal units of a rational normalized completion have spectral norm
`≤ 1 / p` (the p-adic contraction bound). -/
theorem principal_unit_norm_le_inv_prime (P : NumberField.FinitePlace ℚ)
    (x : (Integers (NormalizedCompletion P))ˣ)
    (hx : x ∈ principalUnits (K := NormalizedCompletion P)) :
    ‖(((x.val : Integers (NormalizedCompletion P)) : NormalizedCompletion P) - 1)‖ ≤
      ((completionRationalPrime P).val : ℝ)⁻¹ := by
  let y : NormalizedCompletion P :=
    ((x.val : Integers (NormalizedCompletion P)) : NormalizedCompletion P) - 1
  have hlt : ‖y‖ < 1 := principal_unit_norm_lt_one P x hx
  let c : PadicScalarField P := normalizedCompletionPadicEquiv P y
  have hc : ‖c‖ < 1 := by
    rw [← norm_eq_padic P y]
    exact hlt
  have hle : ‖c‖ ≤ ((completionRationalPrime P).val : ℝ) ^ (-1 : ℤ) := by
    rw [Padic.norm_le_pow_iff_norm_lt_pow_add_one]
    simpa using hc
  have hle' : ‖c‖ ≤ ((completionRationalPrime P).val : ℝ)⁻¹ := by
    simpa [zpow_neg_one] using hle
  rwa [show ‖y‖ = ‖c‖ from by rw [norm_eq_padic P y]]

/-- For `p ≥ 3`, principal units satisfy the strict `1/3` radius needed by the
`log1p` estimate. -/
theorem principal_unit_norm_le_third (P : NumberField.FinitePlace ℚ)
    (h3 : 3 ≤ (completionRationalPrime P).val)
    (x : (Integers (NormalizedCompletion P))ˣ)
    (hx : x ∈ principalUnits (K := NormalizedCompletion P)) :
    ‖(((x.val : Integers (NormalizedCompletion P)) : NormalizedCompletion P) - 1)‖ ≤ 1 / 3 := by
  have hbound := principal_unit_norm_le_inv_prime P x hx
  have hp3 : (3 : ℝ) ≤ ((completionRationalPrime P).val : ℝ) := by exact_mod_cast h3
  have hinv : ((completionRationalPrime P).val : ℝ)⁻¹ ≤ 1 / 3 := by
    rw [← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hp3
  exact hbound.trans hinv

end LeanFormal.IUT.XiFPaper.NormalizedCompletionPadicBridgeActual
