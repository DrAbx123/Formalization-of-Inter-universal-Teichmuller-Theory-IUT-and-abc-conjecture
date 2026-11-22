import tmp.sheaf.n8.closure.PaperKfUniformizerRelationActual
import tmp.sheaf.n8.closure.PaperKfQOScalingGeneral
import tmp.sheaf.n8.closure.PaperKfDVRGeneric

/-!
# PaperKf qO scaling closed

Actual uniformizer relation from positivity and DVR decomposition; then the
general q norm-power formula and `PaperKfQORegionScaling`. -/

noncomputable section
set_option maxHeartbeats 4000000
set_option relaxedAutoImplicit false

namespace LeanFormal.IUT.N8Closure.PaperKfQOScalingClosed

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.PaperKfDVRGeneric
open LeanFormal.IUT.N8Closure.PaperKfUniformizerRelationActual
open LeanFormal.IUT.N8Closure.PaperKfHaarNormActual
open LeanFormal.IUT.N8Closure.PaperKfQOScalingGeneral
open LeanFormal.IUT.N8Closure.EtaHaarCharNormIdentification
open LeanFormal.IUT.N8Closure.EtaQHaarScalingCalibration
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise NNReal

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev PaperKf : Type := CommonPrimeCompletion (placeAtPrime S)

local instance : MeasurableSpace (PaperKf S) := borel _
local instance : BorelSpace (PaperKf S) := ⟨rfl⟩

theorem unit_inv_smul_O {u : (PaperKf S)ˣ}
    (hu : u • (Integers (PaperKf S) : Set (PaperKf S)) =
      (Integers (PaperKf S) : Set (PaperKf S))) :
    u⁻¹ • (Integers (PaperKf S) : Set (PaperKf S)) =
      (Integers (PaperKf S) : Set (PaperKf S)) := by
  have h := congrArg (fun T : Set (PaperKf S) => u⁻¹ • T) hu
  rwa [smul_smul, inv_mul_cancel, one_smul] at h

theorem mK_eq_one_of_O {u : (PaperKf S)ˣ}
    (hu : u • (Integers (PaperKf S) : Set (PaperKf S)) =
      (Integers (PaperKf S) : Set (PaperKf S))) :
    mK (K := PaperKf S) u = 1 := by
  let μ : Measure (PaperKf S) := Measure.addHaar
  have hO := measure_O_pos_lt_top (K := PaperKf S) μ
  have hmeasure : μ (u • O (PaperKf S)) = (1 : ENNReal) * μ (O (PaperKf S)) := by
    rw [show u • O (PaperKf S) = (Integers (PaperKf S) : Set (PaperKf S)) from hu]
    simp
  have hchar : (distribHaarChar (PaperKf S)) u = 1 :=
    distribHaarChar_eq_of_measure_smul_eq_mul (A := PaperKf S) (μ := μ)
      hO.1.ne' hO.2.ne hmeasure
  unfold mK
  rw [hchar]
  norm_num

/-- Actual uniformizer power relation from positivity. -/
theorem uniformizer_power_relation :
    ∃ (e : ℕ) (u : (PaperKf S)ˣ), e ≠ 0 ∧
      (paperUniformizerUnit S) ^ e = paperPrimeUnit S * u ∧
      u • (Integers (PaperKf S) : Set (PaperKf S)) =
        (Integers (PaperKf S) : Set (PaperKf S)) ∧
      ‖(u : PaperKf S)‖ = 1 := by
  rcases exists_paperQ_decomposition S (paperPrimeUnit S) with ⟨z, u0, hq, hu0O, hu0norm⟩
  have hzpos : 0 < z := missingPositiveUniformizerExponent_actual S
    (paperPrimeUnit S) rfl z u0 hq hu0O hu0norm
  let e : ℕ := z.toNat
  have hez : (e : ℤ) = z := Int.toNat_of_nonneg hzpos.le
  have hene : e ≠ 0 := by
    intro he
    have : z = 0 := by simpa [he] using hez.symm
    linarith
  let u : (PaperKf S)ˣ := u0⁻¹
  refine ⟨e, u, hene, ?_, ?_, ?_⟩
  · rw [hq, ← hez]
    dsimp [u]
    group
  · exact unit_inv_smul_O S hu0O
  · dsimp [u]
    rw [norm_inv, hu0norm, inv_one]

theorem haarNorm_paperUniformizer :
    mK (K := PaperKf S) (paperUniformizerUnit S) =
      ‖((paperUniformizerUnit S : (PaperKf S)ˣ) : PaperKf S)‖ ^ C7QPilotMassActual.d S := by
  rcases uniformizer_power_relation S with ⟨e, u, he, hrel, huO, hunorm⟩
  exact paperKf_mK_uniformizer_of_relation S (paperUniformizerUnit S) u e he hrel huO hunorm

theorem haarNormIdentificationTarget_actual :
    HaarNormIdentificationTarget (K := PaperKf S) (p := pNat S) := by
  intro q
  rcases exists_paperQ_decomposition S q with ⟨z, u, hq, huO, hunorm⟩
  rw [hq]
  rw [show mK (K := PaperKf S) (u * paperUniformizerUnit S ^ z) =
      mK (K := PaperKf S) u * mK (K := PaperKf S) (paperUniformizerUnit S ^ z) from
    map_mul (mK (K := PaperKf S)) u (paperUniformizerUnit S ^ z)]
  rw [map_zpow]
  rw [mK_eq_one_of_O S huO, one_mul, haarNorm_paperUniformizer S]
  rw [Units.val_mul, norm_mul, hunorm, one_mul, Units.val_zpow_eq_zpow_val]
  rw [norm_zpow]
  rw [localDimension_eq_d S]
  rw [← mul_pow]
  ring_nf

theorem paperKfQORegionScaling_actual :
    ∀ q : (PaperKf S)ˣ, PaperKfQORegionScaling S q :=
  paperKfQORegionScaling_of_haarNorm S (haarNormIdentificationTarget_actual S)

end LeanFormal.IUT.N8Closure.PaperKfQOScalingClosed

end