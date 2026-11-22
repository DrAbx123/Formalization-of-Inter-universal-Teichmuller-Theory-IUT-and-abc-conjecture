import tmp.sheaf.n8.closure.C7QPilotRegionActual
import tmp.sheaf.n8.closure.EtaQOAddHaarNormalizedCalibrationActual

/-!
# C7 q-pilot mass actual

Transport the actual q-pilot region across the one-factor equivalence to the
Kf scaled integral region, and isolate the exact missing mass comparison.
The actual Kf normalized-Haar formula gives `μK(qO).toReal = ‖q‖^d`, hence a
log readout `d * log‖q‖`.  Therefore the paper `log q` readout is
`QPaper / d`, not `QPaper`, unless the normalization already absorbs `d`.
-/

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.C7QPilotMassActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

/-- Actual q-scaled integral region in Kf. -/
noncomputable def qScaledIntegersRegion :
    Set (CommonPrimeCompletion (placeAtPrime S)) :=
  Set.image (fun x => qAtPrime S * x)
    (Integers (CommonPrimeCompletion (placeAtPrime S)) : Set _)

/-- The one-factor equivalence identifies the tensor q-pilot region with the
actual Kf q-scaled integral region. -/
theorem e_image_qPilotRegion :
    Set.image (fun y => e S y) (qPilotRegion S) = qScaledIntegersRegion S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    rcases hz with ⟨w, hw, rfl⟩
    exact ⟨w, hw, ((e S).apply_symm_apply (qAtPrime S * w)).symm⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(e S).symm (qAtPrime S * z), ?_, (e S).apply_symm_apply _⟩
    exact ⟨qAtPrime S * z, ⟨z, hz, rfl⟩, rfl⟩

/-- The degree of the one-factor Kf block. -/
noncomputable def d : ℕ :=
  Module.finrank ℚ_[pNat S] (CommonPrimeCompletion (placeAtPrime S))

theorem d_pos : 0 < d S := Module.finrank_pos

/-- The paper log-q proposal: Kf normalized log readout divided by the block
degree. -/
noncomputable def QPaperPerDegree : ℝ :=
  QPaper S / (d S : ℝ)

theorem d_ne_zero_real : (d S : ℝ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (d_pos S))

/-- Exact log readout gap without choosing the d-normalization. -/
def QPaperEqLogNorm : Prop := QPaper S = Real.log ‖q S‖

/-- Exact d-normalized paper log-q readout. -/
def QPaperPerDegreeEqLogNorm : Prop := QPaperPerDegree S = Real.log ‖q S‖

end LeanFormal.IUT.N8Closure.C7QPilotMassActual

end