import tmp.sheaf.xif.paper.PaperRootExtensionDiscreteValuationActual
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Actual prime/uniformizer decomposition in L -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

noncomputable section
open scoped BigOperators Pointwise NNReal Valued

namespace LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeDecompositionActual

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

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Multiplication by a Qp scalar has the expected norm (local NormSMulClass). -/
theorem rootNorm_algebraMap_prime :
    ‖(algebraMap ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
      (qVFamTensorP T b) : rootNormedExtension T b)‖ =
      ‖(qVFamTensorP T b : ℚ_[(qVFamTensorP T b)])‖ := by
  letI : NormedSpace ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
    rootNormedExtensionNormedSpaceQp (T := T) (b := b)
  letI : IsBoundedSMul ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
    NormedSpace.toIsBoundedSMul
  letI : NormSMulClass ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
    NormedDivisionRing.toNormSMulClass
  rw [Algebra.algebraMap_eq_smul_one, norm_smul, norm_one, mul_one]

/-- The image of the rational prime lies in the actual integer ring. -/
theorem root_prime_mem_integers :
    (algebraMap ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
      (qVFamTensorP T b) : rootNormedExtension T b) ∈
      Integers (rootNormedExtension T b) := by
  rw [mem_integers_iff]
  rw [rootNorm_algebraMap_prime (T := T) (b := b)]
  exact (Padic.norm_p_lt_one (p := qVFamTensorP T b)).le

/-- The prime element as an element of the integer ring. -/
noncomputable def rootPrimeInteger :
    Integers (rootNormedExtension T b) :=
  ⟨(algebraMap ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
      (qVFamTensorP T b) : rootNormedExtension T b),
    root_prime_mem_integers (T := T) (b := b)⟩

/-- The prime integer is nonzero. -/
theorem rootPrimeInteger_ne_zero : rootPrimeInteger T b ≠ 0 := by
  intro hzero
  have hval : (algebraMap ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
      (qVFamTensorP T b) : rootNormedExtension T b) = 0 := by
    simpa [rootPrimeInteger] using congrArg Subtype.val hzero
  exact (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime (qVFamTensorP T b)).ne_zero)
    ((algebraMap ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)).injective
      (by simpa using hval))

/-- Actual decomposition p = u * pi^e in the integer ring. -/
structure RootPrimeUniformizerDecomposition where
  exponent : Nat
  unit : (Integers (rootNormedExtension T b))ˣ
  eq : rootPrimeInteger T b =
    (unit : Integers (rootNormedExtension T b)) * (rootUniformizer T b) ^ exponent

/-- Construct the actual prime-uniformizer decomposition. -/
noncomputable def rootPrimeUniformizerDecomposition :
    RootPrimeUniformizerDecomposition T b :=
  let h := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := rootPrimeInteger T b) (rootPrimeInteger_ne_zero (T := T) (b := b))
    (rootUniformizer_irreducible (T := T) (b := b))
  { exponent := Classical.choose h
    unit := Classical.choose (Classical.choose_spec h)
    eq := Classical.choose_spec (Classical.choose_spec h) }

/-- The actual ramification exponent of p, from the decomposition. -/
def rootPrimeRamificationExponent : Nat :=
  (rootPrimeUniformizerDecomposition T b).exponent

/-- The actual prime-unit part. -/
noncomputable def rootPrimeUnit :
    (Integers (rootNormedExtension T b))ˣ :=
  (rootPrimeUniformizerDecomposition T b).unit

/-- The actual decomposition equation. -/
theorem rootPrime_eq_unit_mul_uniformizer_pow :
    rootPrimeInteger T b =
      (rootPrimeUnit T b : Integers (rootNormedExtension T b)) *
        (rootUniformizer T b) ^ rootPrimeRamificationExponent (T := T) (b := b) :=
  (rootPrimeUniformizerDecomposition T b).eq

end LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeDecompositionActual

end