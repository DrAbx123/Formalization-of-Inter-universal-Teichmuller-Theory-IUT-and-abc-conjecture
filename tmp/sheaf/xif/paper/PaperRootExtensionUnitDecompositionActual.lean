import tmp.sheaf.xif.paper.PaperRootExtensionHaarFactorActual

/-! # Field-unit form of the prime/uniformizer decomposition -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.PaperRootExtensionUnitDecompositionActual
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionValuedActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionDiscreteValuationActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeDecompositionActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarFactorActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The prime unit u as a field unit of L. -/
noncomputable def rootPrimeUnitField : (rootNormedExtension T b)ˣ :=
  Units.mk0 (((rootPrimeUnit T b : Integers (rootNormedExtension T b)) :
    rootNormedExtension T b)) (by
      intro h
      exact Units.ne_zero (rootPrimeUnit T b) (Subtype.ext h))

/-- The uniformizer pi as a field unit of L. -/
noncomputable def rootUniformizerField : (rootNormedExtension T b)ˣ :=
  Units.mk0 ((rootUniformizer T b : Integers (rootNormedExtension T b)) :
    rootNormedExtension T b) (by
      intro h
      exact (rootUniformizer_irreducible (T := T) (b := b)).ne_zero
        (Subtype.ext h))

/-- The prime-unit part has norm one. -/
theorem rootPrimeUnitField_norm : ‖(rootPrimeUnitField T b :
    rootNormedExtension T b)‖ = 1 :=
  norm_unit_eq_one (rootPrimeUnit T b)


/-- Field-unit form of the prime uniformizer decomposition. -/
theorem rootPrimeFieldUnit_eq_unit_mul_uniformizer_pow :
    rootPrimeFieldUnit T b =
      rootPrimeUnitField T b * rootUniformizerField T b ^
        rootPrimeRamificationExponent (T := T) (b := b) := by
  apply Units.ext
  change ((rootPrimeInteger T b : Integers (rootNormedExtension T b)) :
    rootNormedExtension T b) =
    ((rootPrimeUnit T b : Integers (rootNormedExtension T b)) :
      rootNormedExtension T b) *
      (((rootUniformizer T b : Integers (rootNormedExtension T b)) :
        rootNormedExtension T b) ^ rootPrimeRamificationExponent (T := T) (b := b))
  simpa using congrArg (fun x : Integers (rootNormedExtension T b) =>
    (x : rootNormedExtension T b))
    (rootPrime_eq_unit_mul_uniformizer_pow (T := T) (b := b))

/-- The prime field unit has norm below one. -/
theorem rootPrimeFieldUnit_norm_lt_one :
    ‖(rootPrimeFieldUnit T b : rootNormedExtension T b)‖ < 1 := by
  rw [show (rootPrimeFieldUnit T b : rootNormedExtension T b) =
    (algebraMap ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
      (qVFamTensorP T b) : rootNormedExtension T b) from rfl]
  rw [rootNorm_algebraMap_prime (T := T) (b := b)]
  exact Padic.norm_p_lt_one (p := qVFamTensorP T b)

/-- Norm relation: ||p|| = ||pi||^e. -/
theorem rootPrimeFieldUnit_norm_eq_uniformizer_pow :
    ‖(rootPrimeFieldUnit T b : rootNormedExtension T b)‖ =
      ‖(rootUniformizerField T b : rootNormedExtension T b)‖ ^
        rootPrimeRamificationExponent (T := T) (b := b) := by
  conv_lhs => rw [rootPrimeFieldUnit_eq_unit_mul_uniformizer_pow (T := T) (b := b)]
  rw [Units.val_mul, norm_mul, Units.val_pow_eq_pow_val, norm_pow,
    rootPrimeUnitField_norm, one_mul]

/-- The ramification exponent is positive. -/
theorem rootPrimeRamificationExponent_pos :
    0 < rootPrimeRamificationExponent (T := T) (b := b) := by
  by_contra h
  have h0 : rootPrimeRamificationExponent (T := T) (b := b) = 0 := by omega
  have hn : ‖(rootPrimeFieldUnit T b : rootNormedExtension T b)‖ = 1 := by
    rw [rootPrimeFieldUnit_norm_eq_uniformizer_pow (T := T) (b := b), h0, pow_zero]
  have hlt := rootPrimeFieldUnit_norm_lt_one (T := T) (b := b)
  rw [hn] at hlt
  exact lt_irrefl _ hlt


/-- factor(pi)^e = factor(p). -/
theorem rootHaarFactor_uniformizer_pow_eq_prime :
    rootHaarFactor T b (rootUniformizerField T b ^
      rootPrimeRamificationExponent (T := T) (b := b)) =
      rootHaarFactor T b (rootPrimeFieldUnit T b) := by
  conv_rhs => rw [rootPrimeFieldUnit_eq_unit_mul_uniformizer_pow (T := T) (b := b)]
  rw [rootHaarFactor_mul,
    rootHaarFactor_eq_one_of_norm_one (T := T) (b := b) (rootPrimeUnitField T b) (rootPrimeUnitField_norm (T := T) (b := b)),
    one_mul]

/-- factor(p) = ofReal ((||pi||^d)^e). -/
theorem rootHaarFactor_prime_eq_ofReal_uniformizer_pow :
    rootHaarFactor T b (rootPrimeFieldUnit T b) =
      ENNReal.ofReal ((‖(rootUniformizerField T b :
        rootNormedExtension T b)‖ ^ Module.finrank ℚ_[(qVFamTensorP T b)]
          (rootNormedExtension T b)) ^ rootPrimeRamificationExponent (T := T) (b := b)) := by
  rw [rootHaarFactor_prime_eq_norm_pow]
  change ENNReal.ofReal (‖(rootPrimeFieldUnit T b : rootNormedExtension T b)‖ ^
    Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)) = _
  rw [rootPrimeFieldUnit_norm_eq_uniformizer_pow]
  rw [ENNReal.ofReal_pow (by positivity)]
  rw [← ENNReal.ofReal_pow (by positivity)]
  congr 1
  rw [← pow_mul, ← pow_mul]
  ring_nf

end LeanFormal.IUT.XiFPaper.PaperRootExtensionUnitDecompositionActual
end