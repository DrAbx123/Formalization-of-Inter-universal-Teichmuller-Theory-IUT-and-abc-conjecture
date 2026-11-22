import tmp.sheaf.n8.closure.PaperKfUniformizerRelationActual
import tmp.sheaf.n8.closure.EtaQHaarScalingCalibration

set_option maxHeartbeats 4000000
set_option relaxedAutoImplicit false

/-!
# PaperKf Haar norm closed

From the actual positive DVR relation pi^e = pUnit * u, obtain
mK(pi) = ||pi||^d.  Then every q = u_q * pi^z has
mK(q) = mK(u_q) * mK(pi)^z = ||q||^d.  No native X.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.PaperKfHaarNormClosed

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.PaperKfDVRGeneric
open LeanFormal.IUT.N8Closure.PaperKfHaarNormActual
open LeanFormal.IUT.N8Closure.PaperKfUniformizerRelationActual
open LeanFormal.IUT.N8Closure.EtaQHaarScalingCalibration
open LeanFormal.IUT.N8Closure.EtaHaarCharNormIdentification
open LeanFormal.IUT.N8Closure.EtaUniformizerHaarScaling
open LeanFormal.IUT.LocalFieldLogarithm
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise NNReal

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev PaperKf : Type := CommonPrimeCompletion (placeAtPrime S)

local instance : MeasurableSpace (PaperKf S) := borel _
local instance : BorelSpace (PaperKf S) := ⟨rfl⟩

theorem paperKf_mK_eq_one_of_smul_integers (u : (PaperKf S)ˣ)
    (huO : u • (Integers (PaperKf S) : Set (PaperKf S)) =
      (Integers (PaperKf S) : Set (PaperKf S))) :
    mK (K := PaperKf S) u = 1 := by
  let μ : Measure (PaperKf S) := Measure.addHaar
  have hO := measure_localIntegers_pos_lt_top (K := PaperKf S) μ
  have hmeasure : μ (u • (Integers (PaperKf S) : Set (PaperKf S))) =
      (1 : ENNReal) * μ (Integers (PaperKf S) : Set (PaperKf S)) := by
    rw [huO]
    simp
  have hchar : distribHaarChar (PaperKf S) u = 1 :=
    distribHaarChar_eq_of_measure_smul_eq_mul (A := PaperKf S) (μ := μ)
      hO.1.ne' hO.2.ne hmeasure
  unfold mK
  rw [hchar]
  norm_num

theorem paperKf_mK_uniformizer : 
    mK (K := PaperKf S) (PaperKfDVRGeneric.paperUniformizerUnit S) =
      ‖(PaperKfDVRGeneric.paperUniformizerUnit S : PaperKf S)‖ ^
        C7QPilotMassActual.d S := by
  obtain ⟨z, u, hzu, huO, hunorm⟩ :=
    exists_paperQ_decomposition S (paperPrimeUnit S)
  have hzpos : 0 < z :=
    missingPositiveUniformizerExponent_actual S (paperPrimeUnit S) rfl z u hzu huO hunorm
  have huInvO : u⁻¹ • (Integers (PaperKf S) : Set (PaperKf S)) =
      (Integers (PaperKf S) : Set (PaperKf S)) := by
    calc
      u⁻¹ • (Integers (PaperKf S) : Set (PaperKf S)) =
          u⁻¹ • (u • (Integers (PaperKf S) : Set (PaperKf S))) := by rw [huO]
      _ = (Integers (PaperKf S) : Set (PaperKf S)) := by
        rw [Units.smul_def, Units.smul_def, smul_smul, ← Units.val_mul,
          inv_mul_cancel, Units.val_one, one_smul]
  have huInvNorm : ‖((u⁻¹ : (PaperKf S)ˣ) : PaperKf S)‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv, hunorm, inv_one]
  have heq : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (le_of_lt hzpos)
  have hrel : PaperKfDVRGeneric.paperUniformizerUnit S ^ z.toNat =
      paperPrimeUnit S * u⁻¹ := by
    have hzpow : PaperKfDVRGeneric.paperUniformizerUnit S ^ z =
        u⁻¹ * paperPrimeUnit S := by
      rw [hzu, ← mul_assoc, inv_mul_cancel, one_mul]
    calc
      PaperKfDVRGeneric.paperUniformizerUnit S ^ z.toNat =
          PaperKfDVRGeneric.paperUniformizerUnit S ^ z := by
            rw [← zpow_natCast, heq]
      _ = u⁻¹ * paperPrimeUnit S := hzpow
      _ = paperPrimeUnit S * u⁻¹ := mul_comm _ _
  exact paperKf_mK_uniformizer_of_relation S
    (PaperKfDVRGeneric.paperUniformizerUnit S) (u⁻¹) (z.toNat)
    (by omega) hrel huInvO huInvNorm

theorem paperKf_haarNormIdentificationTarget : 
    HaarNormIdentificationTarget (K := PaperKf S) (p := pNat S) := by
  intro q
  obtain ⟨z, u, hq, huO, hunorm⟩ := exists_paperQ_decomposition S q
  have hmK_u : mK (K := PaperKf S) u = 1 :=
    paperKf_mK_eq_one_of_smul_integers S u huO
  have hmK_pi := paperKf_mK_uniformizer S
  have hmK_q : mK (K := PaperKf S) q =
      (mK (K := PaperKf S) (PaperKfDVRGeneric.paperUniformizerUnit S)) ^ z := by
    unfold mK
    rw [hq]
    rw [map_mul]
    have hchar_u : (distribHaarChar (PaperKf S)) u = 1 := by
      unfold mK at hmK_u
      exact_mod_cast hmK_u
    rw [hchar_u]
    rw [map_zpow]
    simp
  have hnorm_q : ‖(q : PaperKf S)‖ =
      ‖(PaperKfDVRGeneric.paperUniformizerUnit S : PaperKf S)‖ ^ z := by
    rw [hq, Units.val_mul, Units.val_zpow_eq_zpow_val, norm_mul, hunorm, one_mul, norm_zpow]
  rw [hmK_q, hmK_pi, hnorm_q]
  rw [PaperKfHaarNormActual.paperKf_localDimension_eq_d S]
  have hpos : 0 < ‖(PaperKfDVRGeneric.paperUniformizerUnit S : PaperKf S)‖ :=
    norm_pos_iff.mpr (Units.ne_zero (PaperKfDVRGeneric.paperUniformizerUnit S))
  rw [← zpow_natCast, ← zpow_natCast]
  exact zpow_comm _ _ _

end LeanFormal.IUT.N8Closure.PaperKfHaarNormClosed

end