import tmp.sheaf.xif.paper.S2736dTLCompactActual
import tmp.sheaf.xif.paper.S2736aCharPKActual

noncomputable section
open scoped NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2736fTensorPKPiecesActual

open MeasureTheory
open LeanFormal.IUT.PadicIntegerProductLattice
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.PadicFiniteCoordinateHaarScaling
open LeanFormal.IUT.XiFPaper.S2736aCharPKActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable (M : ι → Type*) [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)]
variable [∀ i, FiniteDimensional ℚ_[p] (M i)]

local instance tensorMeasurableSpaceF :
    MeasurableSpace (FinitePadicTensor (p := p) M) := borel _

local instance tensorBorelSpaceF :
    BorelSpace (FinitePadicTensor (p := p) M) := ⟨rfl⟩

local instance coordMeasurableSpaceF :
    MeasurableSpace (FinitePadicTensorIndex (p := p) M → ℚ_[p]) := borel _

local instance coordBorelSpaceF :
    BorelSpace (FinitePadicTensorIndex (p := p) M → ℚ_[p]) := ⟨rfl⟩

local instance tensorSetSMulF :
    SMul ℚ_[p]ˣ (Set (FinitePadicTensor (p := p) M)) :=
  ⟨fun u S => (fun x => ((u : ℚ_[p]) • x)) '' S⟩

local instance coordSetSMulF :
    SMul ℚ_[p]ˣ (Set (FinitePadicTensorIndex (p := p) M → ℚ_[p])) :=
  ⟨fun u S => (fun x => ((u : ℚ_[p]) • x)) '' S⟩

theorem tensor_hpre (K : ℤ) :
    (finitePadicTensorCoordinates (p := p) M) ⁻¹'
        (padicPrimeFieldUnit (p := p) ^ K •
          padicIntegerCoordinateLattice (p := p)
            (ι := FinitePadicTensorIndex (p := p) M)) =
      padicPrimeFieldUnit (p := p) ^ K • tensorLattice (p := p) M := by
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


theorem nnnorm_padicPrimeFieldUnit :
    ‖(padicPrimeFieldUnit (p := p) : ℚ_[p])‖₊ = (p : ℝ≥0)⁻¹ := by
  apply NNReal.coe_injective
  push_cast
  rw [show (padicPrimeFieldUnit (p := p) : ℚ_[p]) = (p : ℚ_[p]) from rfl,
    Padic.norm_p]


theorem tensor_Lsm (K : ℤ) :
    MeasurableSet
      (padicPrimeFieldUnit (p := p) ^ K •
        padicIntegerCoordinateLattice (p := p)
          (ι := FinitePadicTensorIndex (p := p) M)) := by
  let pU : ℚ_[p]ˣ := padicPrimeFieldUnit (p := p)
  let L := padicIntegerCoordinateLattice (p := p)
    (ι := FinitePadicTensorIndex (p := p) M)
  have hLmeas : MeasurableSet L :=
    (isOpen_padicIntegerCoordinateLattice (p := p)
      (ι := FinitePadicTensorIndex (p := p) M)).measurableSet
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
      change (((((↑pU : ℚ_[p]) ^ K)⁻¹ *
        ((↑pU : ℚ_[p]) ^ K)) • y) ∈ L)
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


theorem tensor_hmapTL
    (c : ℝ≥0∞)
    (hmap : Measure.map (finitePadicTensorCoordinates (p := p) M)
      (Measure.addHaar : Measure (FinitePadicTensor (p := p) M)) =
      c • (Measure.addHaar :
        Measure (FinitePadicTensorIndex (p := p) M → ℚ_[p]))) :
    (Measure.addHaar : Measure (FinitePadicTensor (p := p) M))
        (tensorLattice (p := p) M) =
      c * (Measure.addHaar :
        Measure (FinitePadicTensorIndex (p := p) M → ℚ_[p]))
        (padicIntegerCoordinateLattice (p := p)
          (ι := FinitePadicTensorIndex (p := p) M)) := by
  let L := padicIntegerCoordinateLattice (p := p)
    (ι := FinitePadicTensorIndex (p := p) M)
  have hiso : Isometry (finitePadicTensorCoordinates (p := p) M) := by
    intro x y
    rfl
  have hmeas : Measurable (finitePadicTensorCoordinates (p := p) M) :=
    hiso.continuous.measurable
  have hLmeas : MeasurableSet L :=
    (isOpen_padicIntegerCoordinateLattice (p := p)
      (ι := FinitePadicTensorIndex (p := p) M)).measurableSet
  change (Measure.addHaar : Measure (FinitePadicTensor (p := p) M))
      ((finitePadicTensorCoordinates (p := p) M) ⁻¹' L) =
    c * (Measure.addHaar :
      Measure (FinitePadicTensorIndex (p := p) M → ℚ_[p])) L
  rw [← Measure.map_apply hmeas hLmeas, hmap]
  simp [Measure.smul_apply, smul_eq_mul]

#check tensor_Lsm
#check tensor_hmapTL

#check nnnorm_padicPrimeFieldUnit

#check tensor_hpre
end LeanFormal.IUT.XiFPaper.S2736fTensorPKPiecesActual
end
