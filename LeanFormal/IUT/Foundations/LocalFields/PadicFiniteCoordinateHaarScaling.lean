import LeanFormal.IUT.Foundations.LocalFields.PadicIntegerProductLattice
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

/-!
# The exact Haar p-scaling factor in finite p-adic coordinates

Pull back the ambient Haar measure through the actual open integral
embedding. The residue kernel has index p^d, so its mass is p^(-d) times
the integral lattice mass. Haar uniqueness then supplies this same factor
on every region, with no measurability or positive-mass assumption on it.
-/

namespace LeanFormal.IUT.PadicFiniteCoordinateHaarScaling

open LeanFormal.IUT.PadicIntegerProductLattice MeasureTheory
open scoped Pointwise NNReal ENNReal

noncomputable section

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]

def padicPrimeFieldUnit : ℚ_[p]ˣ :=
  Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero)

section Measure

variable [MeasurableSpace (ι → ℚ_[p])] [BorelSpace (ι → ℚ_[p])]
variable (μ : Measure (ι → ℚ_[p])) [Measure.IsAddHaarMeasure μ]

theorem measure_prime_smul_padicIntegerCoordinateLattice :
    μ ((p : ℚ_[p]) • padicIntegerCoordinateLattice (p := p) (ι := ι)) =
      ((p : ENNReal) ^ Fintype.card ι)⁻¹ * μ (padicIntegerCoordinateLattice (p := p)) := by
  letI : MeasurableSpace (ι → ℤ_[p]) := borel _
  letI : BorelSpace (ι → ℤ_[p]) := ⟨rfl⟩
  let ν := μ.comap (integerProductEmbedding (p := p) (ι := ι))
  have hopen := isOpenEmbedding_integerProductEmbedding (p := p) (ι := ι)
  letI : Measure.IsAddHaarMeasure ν :=
    Measure.IsAddHaarMeasure.comap (mH := inferInstance) μ hopen
  have hmass := MeasureTheory.AddSubgroup.index_mul_measure
    (integerProductResidueHom (p := p) (ι := ι)).ker
    (isCompact_integerProductResidueHom_ker (p := p) (ι := ι)).isClosed.measurableSet ν
  rw [integerProductResidueHom_ker_index] at hmass
  change ((p ^ Fintype.card ι : ℕ) : ENNReal) *
    (μ.comap integerProductEmbedding)
      ((integerProductResidueHom (p := p) (ι := ι)).ker : Set (ι → ℤ_[p])) =
    (μ.comap integerProductEmbedding) Set.univ at hmass
  rw [hopen.measurableEmbedding.comap_apply, hopen.measurableEmbedding.comap_apply,
    image_integerProductResidueHom_ker, Set.image_univ, Nat.cast_pow] at hmass
  change (p : ENNReal) ^ Fintype.card ι *
    μ ((p : ℚ_[p]) • padicIntegerCoordinateLattice (p := p)) =
      μ (padicIntegerCoordinateLattice (p := p)) at hmass
  have hfactor : (p : ENNReal) ^ Fintype.card ι ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero)
  have hfactorfin : (p : ENNReal) ^ Fintype.card ι ≠ ⊤ := by
    rw [← Nat.cast_pow]
    simp
  calc
    μ ((p : ℚ_[p]) • padicIntegerCoordinateLattice (p := p)) =
        ((p : ENNReal) ^ Fintype.card ι)⁻¹ *
          ((p : ENNReal) ^ Fintype.card ι *
            μ ((p : ℚ_[p]) • padicIntegerCoordinateLattice (p := p))) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hfactor hfactorfin, one_mul]
    _ = _ := by rw [hmass]

end Measure

theorem distribHaarChar_prime_finiteCoordinates :
    distribHaarChar (ι → ℚ_[p]) (padicPrimeFieldUnit (p := p)) =
      ((p : ℝ≥0) ^ Fintype.card ι)⁻¹ := by
  letI : MeasurableSpace (ι → ℚ_[p]) := borel _
  letI : BorelSpace (ι → ℚ_[p]) := ⟨rfl⟩
  let μ : Measure (ι → ℚ_[p]) := Measure.addHaar
  have hpos : 0 < μ (padicIntegerCoordinateLattice (p := p) (ι := ι)) :=
    (isOpen_padicIntegerCoordinateLattice (p := p) (ι := ι)).measure_pos μ
      ⟨0, zero_mem_padicIntegerCoordinateLattice⟩
  have hfin : μ (padicIntegerCoordinateLattice (p := p) (ι := ι)) < ⊤ :=
    isCompact_padicIntegerCoordinateLattice.measure_lt_top
  have hfactor : (p : ℝ≥0) ^ Fintype.card ι ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero)
  apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hpos.ne' hfin.ne
  change μ ((p : ℚ_[p]) • padicIntegerCoordinateLattice (p := p)) = _
  rw [measure_prime_smul_padicIntegerCoordinateLattice, ENNReal.coe_inv hfactor,
    ENNReal.coe_pow, ENNReal.coe_natCast]

theorem measure_prime_smul_finiteCoordinates
    [MeasurableSpace (ι → ℚ_[p])] [BorelSpace (ι → ℚ_[p])]
    (μ : Measure (ι → ℚ_[p])) [Measure.IsAddHaarMeasure μ] (S : Set (ι → ℚ_[p])) :
    μ ((p : ℚ_[p]) • S) = ((p : ENNReal) ^ Fintype.card ι)⁻¹ * μ S := by
  have hfactor : (p : ℝ≥0) ^ Fintype.card ι ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero)
  have hmass := distribHaarChar_mul μ (padicPrimeFieldUnit (p := p)) S
  rw [distribHaarChar_prime_finiteCoordinates, ENNReal.coe_inv hfactor,
    ENNReal.coe_pow, ENNReal.coe_natCast] at hmass
  exact hmass.symm

end

end LeanFormal.IUT.PadicFiniteCoordinateHaarScaling
