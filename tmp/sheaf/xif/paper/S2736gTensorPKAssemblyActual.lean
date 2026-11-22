import tmp.sheaf.xif.paper.S2736fTensorPKPiecesActual

noncomputable section
open scoped NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2736gTensorPKAssemblyActual

open MeasureTheory
open LeanFormal.IUT.PadicIntegerProductLattice
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.PadicFiniteCoordinateHaarScaling
open LeanFormal.IUT.XiFPaper.S2736fTensorPKPiecesActual
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable (M : ι → Type*) [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)]
variable [∀ i, FiniteDimensional ℚ_[p] (M i)]

local instance tensorSetSMulG :
    SMul ℚ_[p]ˣ (Set (FinitePadicTensor (p := p) M)) :=
  ⟨fun u S => (fun x => ((u : ℚ_[p]) • x)) '' S⟩

local instance coordSetSMulG :
    SMul ℚ_[p]ˣ (Set (FinitePadicTensorIndex (p := p) M → ℚ_[p])) :=
  ⟨fun u S => (fun x => ((u : ℚ_[p]) • x)) '' S⟩

local instance tensorMeasurableSpaceG :
    MeasurableSpace (FinitePadicTensor (p := p) M) := borel _

local instance tensorBorelSpaceG :
    BorelSpace (FinitePadicTensor (p := p) M) := ⟨rfl⟩

local instance coordMeasurableSpaceG :
    MeasurableSpace (FinitePadicTensorIndex (p := p) M → ℚ_[p]) := borel _

local instance coordBorelSpaceG :
    BorelSpace (FinitePadicTensorIndex (p := p) M → ℚ_[p]) := ⟨rfl⟩

theorem tensor_hC (K : ℤ) :
    (Measure.addHaar :
      Measure (FinitePadicTensorIndex (p := p) M → ℚ_[p]))
        (padicPrimeFieldUnit (p := p) ^ K •
          padicIntegerCoordinateLattice (p := p)
            (ι := FinitePadicTensorIndex (p := p) M)) =
      (distribHaarChar (FinitePadicTensorIndex (p := p) M → ℚ_[p])
        (padicPrimeFieldUnit (p := p) ^ K) : ℝ≥0∞) *
      (Measure.addHaar :
        Measure (FinitePadicTensorIndex (p := p) M → ℚ_[p]))
        (padicIntegerCoordinateLattice (p := p)
          (ι := FinitePadicTensorIndex (p := p) M)) := by
  exact (distribHaarChar_mul
    (μ := (Measure.addHaar :
      Measure (FinitePadicTensorIndex (p := p) M → ℚ_[p])))
    (padicPrimeFieldUnit (p := p) ^ K)
    (padicIntegerCoordinateLattice (p := p)
      (ι := FinitePadicTensorIndex (p := p) M))).symm



theorem tensor_hmap_pK (K : ℤ) (c : ℝ≥0∞)
    (hpre : (finitePadicTensorCoordinates (p := p) M) ⁻¹'
        (padicPrimeFieldUnit (p := p) ^ K •
          padicIntegerCoordinateLattice (p := p)
            (ι := FinitePadicTensorIndex (p := p) M)) =
      padicPrimeFieldUnit (p := p) ^ K • tensorLattice (p := p) M)
    (hLsm : MeasurableSet
      (padicPrimeFieldUnit (p := p) ^ K •
        padicIntegerCoordinateLattice (p := p)
          (ι := FinitePadicTensorIndex (p := p) M)))
    (hmap : Measure.map (finitePadicTensorCoordinates (p := p) M)
      (Measure.addHaar : Measure (FinitePadicTensor (p := p) M)) =
      c • (Measure.addHaar :
        Measure (FinitePadicTensorIndex (p := p) M → ℚ_[p]))) :
    (Measure.addHaar : Measure (FinitePadicTensor (p := p) M))
        (padicPrimeFieldUnit (p := p) ^ K • tensorLattice (p := p) M) =
      c * (Measure.addHaar :
        Measure (FinitePadicTensorIndex (p := p) M → ℚ_[p]))
        (padicPrimeFieldUnit (p := p) ^ K •
          padicIntegerCoordinateLattice (p := p)
            (ι := FinitePadicTensorIndex (p := p) M)) := by
  have hiso : Isometry (finitePadicTensorCoordinates (p := p) M) := by
    intro x y
    rfl
  have hmeas : Measurable (finitePadicTensorCoordinates (p := p) M) :=
    hiso.continuous.measurable
  rw [← hpre]
  rw [← Measure.map_apply hmeas hLsm, hmap]
  simp [Measure.smul_apply, smul_eq_mul]

#check tensor_hmap_pK


theorem tensor_hratio (K : ℤ)
    (c : ℝ≥0∞)
    (char : ℝ≥0)
    (hmapTL : (Measure.addHaar : Measure (FinitePadicTensor (p := p) M))
        (tensorLattice (p := p) M) =
      c * (Measure.addHaar :
        Measure (FinitePadicTensorIndex (p := p) M → ℚ_[p]))
        (padicIntegerCoordinateLattice (p := p)
          (ι := FinitePadicTensorIndex (p := p) M)))
    (hmap_pK : (Measure.addHaar : Measure (FinitePadicTensor (p := p) M))
        (padicPrimeFieldUnit (p := p) ^ K • tensorLattice (p := p) M) =
      c * (Measure.addHaar :
        Measure (FinitePadicTensorIndex (p := p) M → ℚ_[p]))
        (padicPrimeFieldUnit (p := p) ^ K •
          padicIntegerCoordinateLattice (p := p)
            (ι := FinitePadicTensorIndex (p := p) M)))
    (hC : (Measure.addHaar :
        Measure (FinitePadicTensorIndex (p := p) M → ℚ_[p]))
        (padicPrimeFieldUnit (p := p) ^ K •
          padicIntegerCoordinateLattice (p := p)
            (ι := FinitePadicTensorIndex (p := p) M)) =
      (char : ℝ≥0∞) *
        (Measure.addHaar :
          Measure (FinitePadicTensorIndex (p := p) M → ℚ_[p]))
          (padicIntegerCoordinateLattice (p := p)
            (ι := FinitePadicTensorIndex (p := p) M))) :
    (Measure.addHaar : Measure (FinitePadicTensor (p := p) M))
        (padicPrimeFieldUnit (p := p) ^ K • tensorLattice (p := p) M) =
      (char : ℝ≥0∞) *
        (Measure.addHaar : Measure (FinitePadicTensor (p := p) M))
          (tensorLattice (p := p) M) := by
  rw [hmap_pK, hC, hmapTL]
  ac_rfl

#check tensor_hratio


theorem tensor_hmain (K : ℤ) (char : ℝ≥0)
    (hratio : (Measure.addHaar : Measure (FinitePadicTensor (p := p) M))
        (padicPrimeFieldUnit (p := p) ^ K • tensorLattice (p := p) M) =
      (char : ℝ≥0∞) *
        (Measure.addHaar : Measure (FinitePadicTensor (p := p) M))
          (tensorLattice (p := p) M)) :
    distribHaarChar (FinitePadicTensor (p := p) M)
      (padicPrimeFieldUnit (p := p) ^ K) = char := by
  exact distribHaarChar_eq_of_measure_smul_eq_mul
    (μ := (Measure.addHaar : Measure (FinitePadicTensor (p := p) M)))
    (tensorLattice_measure_pos (p := p) M _).ne'
    (tensorLattice_measure_lt_top (p := p) M _).ne hratio

#check tensor_hmain

#check tensor_hC
end LeanFormal.IUT.XiFPaper.S2736gTensorPKAssemblyActual
end
