import LeanFormal.IUT.Foundations.LocalFields.PadicFiniteCoordinateHaarScaling
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Haar p-scaling on an actual finite-dimensional Qp space

A finite basis gives a genuine continuous linear equivalence with finite
p-adic coordinates. Pushing the actual Haar measure through it transports
the proved coordinate formula; no lattice, determinant law, or modulus is
assumed as an interface field.
-/

namespace LeanFormal.IUT.FinitePadicHaarScaling

open MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

variable {p : ℕ} [Fact p.Prime] {M : Type*} [NormedAddCommGroup M]
variable [NormedSpace ℚ_[p] M] [FiniteDimensional ℚ_[p] M]
variable [MeasurableSpace M] [BorelSpace M]

theorem measure_prime_smul_finiteDimensional
    (μ : Measure M) [Measure.IsAddHaarMeasure μ] (S : Set M) :
    μ ((p : ℚ_[p]) • S) = ((p : ENNReal) ^ Module.finrank ℚ_[p] M)⁻¹ * μ S := by
  let e : M ≃L[ℚ_[p]] (Fin (Module.finrank ℚ_[p] M) → ℚ_[p]) :=
    (Module.finBasis ℚ_[p] M).equivFun.toContinuousLinearEquiv
  letI : MeasurableSpace (Fin (Module.finrank ℚ_[p] M) → ℚ_[p]) := borel _
  letI : BorelSpace (Fin (Module.finrank ℚ_[p] M) → ℚ_[p]) := ⟨rfl⟩
  let ν := μ.map e
  letI : Measure.IsAddHaarMeasure ν := e.toContinuousAddEquiv.isAddHaarMeasure_map μ
  have hmass (T : Set M) : ν (e '' T) = μ T := by
    change (μ.map e.toHomeomorph.toMeasurableEquiv) (e '' T) = μ T
    rw [MeasurableEquiv.map_apply]
    congr 1
    exact Set.preimage_image_eq _ e.injective
  have himage : e '' ((p : ℚ_[p]) • S) = (p : ℚ_[p]) • (e '' S) := by
    change e '' ((fun x : M => (p : ℚ_[p]) • x) '' S) =
      (fun y => (p : ℚ_[p]) • y) '' (e '' S)
    rw [Set.image_image, Set.image_image]
    congr 1
    funext x
    exact e.map_smul (p : ℚ_[p]) x
  calc
    μ ((p : ℚ_[p]) • S) = ν (e '' ((p : ℚ_[p]) • S)) := (hmass _).symm
    _ = ν ((p : ℚ_[p]) • (e '' S)) := by rw [himage]
    _ = ((p : ENNReal) ^ Module.finrank ℚ_[p] M)⁻¹ * ν (e '' S) := by
      simpa only [Fintype.card_fin] using
        PadicFiniteCoordinateHaarScaling.measure_prime_smul_finiteCoordinates ν (e '' S)
    _ = _ := by rw [hmass]

theorem log_measure_prime_smul_finiteDimensional
    (μ : Measure M) [Measure.IsAddHaarMeasure μ] {S : Set M}
    (hpos : 0 < μ S) (hfin : μ S < ⊤) :
    Real.log (μ ((p : ℚ_[p]) • S)).toReal =
      -(Module.finrank ℚ_[p] M : ℝ) * Real.log (p : ℝ) + Real.log (μ S).toReal := by
  have hfactor : ((p : ℝ) ^ Module.finrank ℚ_[p] M)⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero))
  rw [measure_prime_smul_finiteDimensional]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_natCast]
  rw [Real.log_mul hfactor (ENNReal.toReal_pos hpos.ne' hfin.ne).ne',
    Real.log_inv, Real.log_pow]
  ring

end

end LeanFormal.IUT.FinitePadicHaarScaling
