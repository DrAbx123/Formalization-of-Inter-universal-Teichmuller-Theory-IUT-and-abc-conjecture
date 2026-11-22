import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.PaperThetaRootObstructionActual

/-! # Actual norm bound for the root theta image in L -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.PaperRootExtensionNormBoundActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Hypotheses: the qVFamily q unit has norm at most one in the normalized
completion. -/
def RootQUnitNormLeOne : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    ‖((sourceRootQUnit T b : rootBase T b))‖ ≤ 1

/-- The root element has norm at most one. -/
theorem rootNormedElement_norm_le_one
    (hq : RootQUnitNormLeOne (T := T)) :
    ‖((rootNormedElement T b : rootNormedAmbient T b))‖ ≤ 1 := by
  have hpow := rootNormedElement_pow (T := T) (b := b)
  have h2l : 2 * l.value ≠ 0 := Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  have hnormpow : ‖((rootNormedElement T b : rootNormedAmbient T b))‖ ^ (2 * l.value) ≤ 1 := by
    rw [← norm_pow, hpow]
    simpa [rootNormedAmbient, rootBase, unitToAlgClosed, norm_algebraMap'] using hq b
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) h2l).mp hnormpow

/-- Every root theta value in L has norm at most one. -/
theorem rootNormedThetaValueInL_norm_le_one
    (hq : RootQUnitNormLeOne (T := T)) (j : SignedLabel l.value) :
    ‖(rootNormedThetaValueInL T b j : rootNormedExtension T b)‖ ≤ 1 := by
  change ‖((rootNormedThetaValue T b j : rootNormedAmbient T b))‖ ≤ 1
  unfold rootNormedThetaValue
  rw [norm_zpow]
  have hpos : 0 < ‖((rootNormedElement T b : rootNormedAmbient T b))‖ := by
    rw [norm_pos_iff]
    simpa [rootNormedElement] using Units.ne_zero (sourceRoot T b)
  exact zpow_le_one₀ hpos
    (rootNormedElement_norm_le_one (T := T) (b := b) hq)
    (gaussExponent_nonneg j.1)

/-- The finite product root norm bound follows from the q-unit norm condition. -/
theorem rootExtensionProductNormBound_of_qUnit
    (hq : RootQUnitNormLeOne (T := T)) :
    RootExtensionProductNormBound (T := T) := by
  intro j b
  exact rootNormedThetaValueInL_norm_le_one (T := T) (b := b) hq j

/-- Unconditional root product image containment in the product unit ball,
from the q-unit norm condition. -/
theorem rootExtensionProductThetaImageSet_subset_unitBall_of_qUnit
    (hq : RootQUnitNormLeOne (T := T)) :
    rootExtensionProductThetaImageSet T ⊆ rootExtensionProductUnitBall T :=
  rootExtensionProductThetaImageSet_subset_unitBall (T := T)
    (rootExtensionProductNormBound_of_qUnit (T := T) hq)

end LeanFormal.IUT.XiFPaper.PaperRootExtensionNormBoundActual

end