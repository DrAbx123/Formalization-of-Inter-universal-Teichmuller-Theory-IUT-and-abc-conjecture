import tmp.sheaf.xif.paper.PaperRootExtensionUnitDecompositionActual

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal Valued
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarFactorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionUnitDecompositionActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeDecompositionActual

namespace LeanFormal.IUT.XiFPaper.S284RootUniformizerFactorActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l) (b : Bad (nativePlaceSelection T))

theorem rootHaarFactor_uniformizer_eq_norm_pow :
    rootHaarFactor T b (rootUniformizerField T b) =
      ENNReal.ofReal ((‖(rootUniformizerField T b : rootNormedExtension T b)‖) ^
        Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)) := by
  let e := rootPrimeRamificationExponent (T := T) (b := b)
  have hepos : 0 < e := rootPrimeRamificationExponent_pos (T := T) (b := b)
  have hpow := rootHaarFactor_pow (T := T) (b := b) (rootUniformizerField T b) e
  have hprime := rootHaarFactor_uniformizer_pow_eq_prime (T := T) (b := b)
  have hval := rootHaarFactor_prime_eq_ofReal_uniformizer_pow (T := T) (b := b)
  have hE : (rootHaarFactor T b (rootUniformizerField T b)) ^ e =
      ENNReal.ofReal (((‖(rootUniformizerField T b : rootNormedExtension T b)‖) ^
        Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)) ^ e) := by
    rw [← hpow, hprime, hval]
  have hne_top : rootHaarFactor T b (rootUniformizerField T b) ≠ ⊤ := by
    unfold rootHaarFactor
    exact ENNReal.coe_ne_top
  have hpos : 0 < (rootHaarFactor T b (rootUniformizerField T b)).toReal := by
    rw [ENNReal.toReal_pos_iff]
    refine ⟨?_, lt_top_iff_ne_top.mpr hne_top⟩
    unfold rootHaarFactor
    exact_mod_cast (distribHaarChar_pos (A := rootNormedExtension T b) (g := rootUniformizerField T b))
  have hEreal : ((rootHaarFactor T b (rootUniformizerField T b)).toReal) ^ e =
      (((‖(rootUniformizerField T b : rootNormedExtension T b)‖) ^
        Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)) ^ e) := by
    have h := congrArg ENNReal.toReal hE
    have hnonneg : (0 : ℝ) ≤ ((‖(rootUniformizerField T b : rootNormedExtension T b)‖) ^
        Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)) ^ e := by positivity
    simpa [ENNReal.toReal_pow, ENNReal.toReal_ofReal hnonneg, hne_top] using h
  have hnonneg : 0 ≤ ((rootHaarFactor T b (rootUniformizerField T b)).toReal) := le_of_lt hpos
  have hbase_nonneg : 0 ≤ (‖(rootUniformizerField T b : rootNormedExtension T b)‖) ^
        Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) := by positivity
  have hbase := pow_left_inj₀ hnonneg hbase_nonneg (ne_of_gt hepos) |>.mp hEreal
  calc
    rootHaarFactor T b (rootUniformizerField T b)
        = ENNReal.ofReal (rootHaarFactor T b (rootUniformizerField T b)).toReal :=
          (ENNReal.ofReal_toReal hne_top).symm
    _ = ENNReal.ofReal ((‖(rootUniformizerField T b : rootNormedExtension T b)‖) ^
        Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)) := by rw [hbase]

end LeanFormal.IUT.XiFPaper.S284RootUniformizerFactorActual
end