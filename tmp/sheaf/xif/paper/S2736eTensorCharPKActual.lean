import tmp.sheaf.xif.paper.S2736dTLCompactActual
import tmp.sheaf.xif.paper.S2736aCharPKActual

noncomputable section
open scoped NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2736eTensorCharPKActual

open MeasureTheory
open LeanFormal.IUT.PadicIntegerProductLattice
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.PadicFiniteCoordinateHaarScaling
open LeanFormal.IUT.XiFPaper.S2734LatticeActual
open LeanFormal.IUT.XiFPaper.S2736aCharPKActual
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable (M : ι → Type*) [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)]
variable [∀ i, FiniteDimensional ℚ_[p] (M i)]

local instance tensorMeasurableSpaceE :
    MeasurableSpace (FinitePadicTensor (p := p) M) := borel _

local instance tensorBorelSpaceE :
    BorelSpace (FinitePadicTensor (p := p) M) := ⟨rfl⟩

local instance coordMeasurableSpaceE :
    MeasurableSpace (FinitePadicTensorIndex (p := p) M → ℚ_[p]) := borel _

local instance coordBorelSpaceE :
    BorelSpace (FinitePadicTensorIndex (p := p) M → ℚ_[p]) := ⟨rfl⟩

local instance tensorSetSMulE :
    SMul ℚ_[p]ˣ (Set (FinitePadicTensor (p := p) M)) :=
  ⟨fun u S => (fun x => ((u : ℚ_[p]) • x)) '' S⟩

local instance coordSetScalarSMul :
    SMul ℚ_[p] (Set (FinitePadicTensorIndex (p := p) M → ℚ_[p])) :=
  ⟨fun a S => (fun x => a • x) '' S⟩

local instance coordSetSMul :
    SMul ℚ_[p]ˣ (Set (FinitePadicTensorIndex (p := p) M → ℚ_[p])) :=
  ⟨fun u S => (fun x => ((u : ℚ_[p]) • x)) '' S⟩

theorem tensor_char_pK (K : ℤ) :
    distribHaarChar (FinitePadicTensor (p := p) M)
      (padicPrimeFieldUnit (p := p) ^ K) =
      ((‖(padicPrimeFieldUnit (p := p) : ℚ_[p])‖₊) ^
        Fintype.card (FinitePadicTensorIndex (p := p) M)) ^ K := by
  let pU : ℚ_[p]ˣ := padicPrimeFieldUnit (p := p)
  let pUq : ℚ_[p] := (pU : ℚ_[p])
  let L := padicIntegerCoordinateLattice (p := p)
    (ι := FinitePadicTensorIndex (p := p) M)
  let μT : Measure (FinitePadicTensor (p := p) M) := Measure.addHaar
  let μC : Measure (FinitePadicTensorIndex (p := p) M → ℚ_[p]) :=
    Measure.addHaar
  have hiso : Isometry (finitePadicTensorCoordinates (p := p) M) := by
    intro x y
    rfl
  have hmeas : Measurable (finitePadicTensorCoordinates (p := p) M) :=
    hiso.continuous.measurable
  have hLmeas : MeasurableSet L :=
    (isOpen_padicIntegerCoordinateLattice (p := p)
      (ι := FinitePadicTensorIndex (p := p) M)).measurableSet
  obtain ⟨c, hc0, hmap⟩ := tensor_haar_map_exists (p := p) M
  have hcfin := tensor_haar_scale_lt_top (p := p) M c hc0 hmap
  have hmapTL : μT (tensorLattice (p := p) M) = c * μC L := by
    change μT ((finitePadicTensorCoordinates (p := p) M) ⁻¹' L) =
      c * μC L
    rw [← Measure.map_apply hmeas hLmeas, hmap]
    rw [Measure.smul_apply, smul_eq_mul]
  have hpre :
      (finitePadicTensorCoordinates (p := p) M) ⁻¹' (pU ^ K • L) =
        pU ^ K • tensorLattice (p := p) M := by
    ext x
    simp only [Set.mem_preimage, Set.mem_smul_set]
    constructor
    · rintro ⟨y, hy, hxy⟩
      simp only [Units.smul_def] at hxy
      refine ⟨(finitePadicTensorCoordinates (p := p) M).symm y, ?_, ?_⟩
      · rw [tensorLattice_mem_iff]
        simpa using hy
      · apply (finitePadicTensorCoordinates (p := p) M).injective
        simp only [Units.smul_def]
        rw [map_smul, LinearEquiv.apply_symm_apply]
        exact hxy
    · rintro ⟨z, hz, rfl⟩
      simp only [Units.smul_def]
      refine ⟨(finitePadicTensorCoordinates (p := p) M) z, ?_, ?_⟩
      · rwa [tensorLattice_mem_iff] at hz
      · rw [map_smul]

  have hLsm : MeasurableSet (pU ^ K • L) := by
    have hset : (pU ^ K • L) =
        (fun x => (((pU ^ K : ℚ_[p])⁻¹) • x)) ⁻¹' L := by
      ext x
      rw [Set.mem_preimage, Set.mem_smul_set]
      constructor
      · rintro ⟨y, hy, hxy⟩
        rw [← hxy]
        simp only [Units.smul_def]
        rw [show (↑(pU ^ K) : ℚ_[p]) = (↑pU : ℚ_[p]) ^ K by
          rw [Units.val_zpow_eq_zpow_val]]
        have ha : (↑pU : ℚ_[p]) ^ K ≠ 0 :=
          zpow_ne_zero _ (Units.ne_zero pU)
        rw [smul_smul]
        change (((((↑pU : ℚ_[p]) ^ K)⁻¹ * ((↑pU : ℚ_[p]) ^ K)) • y) ∈ L)
        rw [inv_mul_cancel₀ ha, one_smul]
        exact hy
      · intro hx
        refine ⟨(((pU ^ K : ℚ_[p])⁻¹) • x), ?_, ?_⟩
        · simpa only [Units.smul_def] using hx
        · simp only [Units.smul_def]
          rw [smul_smul]
          rw [show (↑(pU ^ K) : ℚ_[p]) = (↑pU : ℚ_[p]) ^ K by
            rw [Units.val_zpow_eq_zpow_val]]
          rw [mul_inv_cancel₀]
          · rw [one_smul]
          · exact zpow_ne_zero _ (Units.ne_zero pU)
    rw [hset]
    exact hLmeas.preimage (continuous_const_smul _).measurable

  have hmap_pK :
      μT (pU ^ K • tensorLattice (p := p) M) =
        c * μC (pU ^ K • L) := by
    rw [← hpre]
    rw [← Measure.map_apply hmeas hLsm, hmap]
    rw [Measure.smul_apply, smul_eq_mul]
  have hC : μC (pU ^ K • L) =
      (distribHaarChar (FinitePadicTensorIndex (p := p) M → ℚ_[p])
        (pU ^ K) : ℝ≥0∞) * μC L := by
    exact (distribHaarChar_mul (μ := μC) (pU ^ K) L).symm
  have hratio :
      μT (pU ^ K • tensorLattice (p := p) M) =
        (distribHaarChar (FinitePadicTensorIndex (p := p) M → ℚ_[p])
          (pU ^ K) : ℝ≥0∞) * μT (tensorLattice (p := p) M) := by
    rw [hmap_pK, hC, hmapTL]
    ac_rfl
  have hmain :
      distribHaarChar (FinitePadicTensor (p := p) M) (pU ^ K) =
        distribHaarChar (FinitePadicTensorIndex (p := p) M → ℚ_[p])
          (pU ^ K) :=
    distribHaarChar_eq_of_measure_smul_eq_mul (μ := μT)
      (tensorLattice_measure_pos (p := p) M μT).ne'
      (tensorLattice_measure_lt_top (p := p) M μT).ne hratio
  rw [hmain]
  have hcoord :
      distribHaarChar (FinitePadicTensorIndex (p := p) M → ℚ_[p])
        (pU ^ K) =
        ((p : ℝ≥0) ^ Fintype.card (FinitePadicTensorIndex (p := p) M))⁻¹ ^ K := by
    exact char_pK (p := p) (ι := FinitePadicTensorIndex (p := p) M) K
  rw [hcoord]
  have hnorm :
      ‖(padicPrimeFieldUnit (p := p) : ℚ_[p])‖₊ = (p : ℝ≥0)⁻¹ := by
    apply NNReal.coe_injective
    push_cast
    rw [show (padicPrimeFieldUnit (p := p) : ℚ_[p]) = (p : ℚ_[p]) from rfl,
      Padic.norm_p]
  rw [hnorm, inv_pow]

#check tensor_char_pK
end LeanFormal.IUT.XiFPaper.S2736eTensorCharPKActual
end
