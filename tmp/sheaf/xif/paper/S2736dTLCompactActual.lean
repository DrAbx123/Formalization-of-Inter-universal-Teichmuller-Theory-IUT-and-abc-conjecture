import tmp.sheaf.xif.paper.S2736cTensorLatticeActual
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S2736dTLCompactActual

open MeasureTheory
open scoped ENNReal
open LeanFormal.IUT.PadicIntegerProductLattice
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2734LatticeActual

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable (M : ι → Type*) [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)]
variable [∀ i, FiniteDimensional ℚ_[p] (M i)]

local instance tensorMeasurableSpace :
    MeasurableSpace (FinitePadicTensor (p := p) M) := borel _

local instance tensorBorelSpace :
    BorelSpace (FinitePadicTensor (p := p) M) := ⟨rfl⟩

local instance coordMeasurableSpace :
    MeasurableSpace (FinitePadicTensorIndex (p := p) M → ℚ_[p]) := borel _

local instance coordBorelSpace :
    BorelSpace (FinitePadicTensorIndex (p := p) M → ℚ_[p]) := ⟨rfl⟩

theorem tensorLattice_compact :
    IsCompact (tensorLattice (p := p) M) := by
  have hiso : Isometry (finitePadicTensorCoordinates (p := p) M) := by
    intro x y
    rfl
  have hbij := (finitePadicTensorCoordinates (p := p) M).bijective
  let hhomeo : FinitePadicTensor (p := p) M ≃ₜ
      (FinitePadicTensorIndex (p := p) M → ℚ_[p]) :=
    hiso.isEmbedding.toHomeomorphOfSurjective
      (finitePadicTensorCoordinates (p := p) M).surjective
  exact hhomeo.isCompact_preimage.mpr
    (isCompact_padicIntegerCoordinateLattice (p := p)
      (ι := FinitePadicTensorIndex (p := p) M))


theorem tensorLattice_isOpen :
    IsOpen (tensorLattice (p := p) M) := by
  have hiso : Isometry (finitePadicTensorCoordinates (p := p) M) := by
    intro x y
    rfl
  let hhomeo : FinitePadicTensor (p := p) M ≃ₜ
      (FinitePadicTensorIndex (p := p) M → ℚ_[p]) :=
    hiso.isEmbedding.toHomeomorphOfSurjective
      (finitePadicTensorCoordinates (p := p) M).surjective
  exact hhomeo.isOpen_preimage.mpr
    (isOpen_padicIntegerCoordinateLattice (p := p)
      (ι := FinitePadicTensorIndex (p := p) M))

theorem tensorLattice_zero_mem :
    (0 : FinitePadicTensor (p := p) M) ∈ tensorLattice (p := p) M := by
  rw [tensorLattice_mem_iff]
  simpa using zero_mem_padicIntegerCoordinateLattice
    (p := p) (ι := FinitePadicTensorIndex (p := p) M)


theorem tensorLattice_measure_pos
    (μ : Measure (FinitePadicTensor (p := p) M)) [μ.IsOpenPosMeasure] :
    0 < μ (tensorLattice (p := p) M) :=
  IsOpen.measure_pos μ (tensorLattice_isOpen (p := p) M)
    ⟨0, tensorLattice_zero_mem (p := p) M⟩

theorem tensorLattice_measure_lt_top
    (μ : Measure (FinitePadicTensor (p := p) M))
    [IsFiniteMeasureOnCompacts μ] :
    μ (tensorLattice (p := p) M) < ⊤ :=
  IsCompact.measure_lt_top (tensorLattice_compact (p := p) M)

#check tensorLattice_measure_pos
#check tensorLattice_measure_lt_top

#check tensorLattice_isOpen


local instance tensorSetSMulD :
    SMul ℚ_[p]ˣ (Set (FinitePadicTensor (p := p) M)) :=
  ⟨fun u S => (fun x => ((u : ℚ_[p]) • x)) '' S⟩

theorem tensor_unit_char_eq_one (w : (PadicInt p)ˣ) :
    distribHaarChar (FinitePadicTensor (p := p) M)
      (unitQHom (p := p) w) = 1 := by
  let μ : Measure (FinitePadicTensor (p := p) M) := Measure.addHaar
  apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (r := 1)
  · exact (tensorLattice_measure_pos (p := p) M μ).ne'
  · exact (tensorLattice_measure_lt_top (p := p) M μ).ne
  · rw [tensorLattice_unit_smul_eq]
    simp

#check tensor_unit_char_eq_one


theorem tensor_haar_map_exists :
    ∃ c : ℝ≥0∞, 0 < c ∧
      Measure.map (finitePadicTensorCoordinates (p := p) M)
        (Measure.addHaar : Measure (FinitePadicTensor (p := p) M)) =
      c • (Measure.addHaar :
        Measure (FinitePadicTensorIndex (p := p) M → ℚ_[p])) := by
  rcases LinearMap.exists_map_addHaar_eq_smul_addHaar
    (L := (finitePadicTensorCoordinates (p := p) M).toLinearMap)
    (μ := (Measure.addHaar : Measure (FinitePadicTensor (p := p) M)))
    (ν := (Measure.addHaar :
      Measure (FinitePadicTensorIndex (p := p) M → ℚ_[p])))
    (finitePadicTensorCoordinates (p := p) M).surjective with
    ⟨c, hc0, hmap⟩
  exact ⟨c, hc0, hmap⟩

#check tensor_haar_map_exists


theorem tensor_haar_scale_lt_top
    (c : ℝ≥0∞) (hc0 : 0 < c)
    (hmap : Measure.map (finitePadicTensorCoordinates (p := p) M)
      (Measure.addHaar : Measure (FinitePadicTensor (p := p) M)) =
      c • (Measure.addHaar :
        Measure (FinitePadicTensorIndex (p := p) M → ℚ_[p]))) :
    c < ⊤ := by
  have hiso : Isometry (finitePadicTensorCoordinates (p := p) M) := by
    intro x y
    rfl
  have hmeas : Measurable (finitePadicTensorCoordinates (p := p) M) :=
    hiso.continuous.measurable
  let L := padicIntegerCoordinateLattice (p := p)
    (ι := FinitePadicTensorIndex (p := p) M)
  have hLmeas : MeasurableSet L :=
    (isOpen_padicIntegerCoordinateLattice (p := p)
      (ι := FinitePadicTensorIndex (p := p) M)).measurableSet
  have hmapTL :
      (Measure.addHaar : Measure (FinitePadicTensor (p := p) M))
        (tensorLattice (p := p) M) =
      c * (Measure.addHaar :
        Measure (FinitePadicTensorIndex (p := p) M → ℚ_[p])) L := by
    change (Measure.addHaar : Measure (FinitePadicTensor (p := p) M))
      ((finitePadicTensorCoordinates (p := p) M) ⁻¹' L) =
      c * (Measure.addHaar :
        Measure (FinitePadicTensorIndex (p := p) M → ℚ_[p])) L
    rw [← Measure.map_apply hmeas hLmeas, hmap]
    simp [Measure.smul_apply, smul_eq_mul]
  have hposL : 0 <
      (Measure.addHaar :
        Measure (FinitePadicTensorIndex (p := p) M → ℚ_[p])) L :=
    IsOpen.measure_pos _ (isOpen_padicIntegerCoordinateLattice (p := p)
      (ι := FinitePadicTensorIndex (p := p) M))
      ⟨0, zero_mem_padicIntegerCoordinateLattice (p := p)
        (ι := FinitePadicTensorIndex (p := p) M)⟩
  by_contra hc
  rw [not_lt] at hc
  have htop : c = ⊤ := top_unique hc
  rw [htop, ENNReal.top_mul (ne_of_gt hposL)] at hmapTL
  exact (ne_of_lt (tensorLattice_measure_lt_top (p := p) M _)) hmapTL

#check tensor_haar_scale_lt_top

end LeanFormal.IUT.XiFPaper.S2736dTLCompactActual
end
