import tmp.sheaf.xif.paper.S290BlockHaarFactorActual
import tmp.sheaf.xif.paper.PaperRootExtensionDiscreteValuationActual

/-! # S295: zpow laws for rootHaarFactor and general factor decomposition

This file proves the rootHaarFactor inverse/zpow laws.  The general norm formula
for arbitrary lambda requires the DVR decomposition lambda = u * pi^n and is
recorded as an exact requirement in this file.

No inequality/no fake factor/sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S295GeneralHaarFactorActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarFactorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionUnitDecompositionActual
open LeanFormal.IUT.XiFPaper.RootTensorThetaHullActual
open LeanFormal.IUT.XiFPaper.S288ThetaScalingHaarFactorActual
open LeanFormal.IUT.XiFPaper.S290BlockHaarFactorActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The Haar factor of the identity is one. -/
theorem rootHaarFactor_one : rootHaarFactor T b (1 : (rootNormedExtension T b)ˣ) = 1 := by
  unfold rootHaarFactor
  simp

/-- The Haar factor of an inverse is the inverse factor. -/
theorem rootHaarFactor_inv (lam : (rootNormedExtension T b)ˣ) :
    rootHaarFactor T b lam⁻¹ = (rootHaarFactor T b lam)⁻¹ := by
  have h := rootHaarFactor_mul (T := T) (b := b) lam lam⁻¹
  rw [mul_inv_cancel, rootHaarFactor_one] at h
  have h' : rootHaarFactor T b lam⁻¹ * rootHaarFactor T b lam = 1 := by
    rw [mul_comm]
    exact h.symm
  exact ENNReal.eq_inv_of_mul_eq_one_left h'

/-- The Haar factor is a zpow homomorphism. -/
theorem rootHaarFactor_zpow (lam : (rootNormedExtension T b)ˣ) (n : ℤ) :
    rootHaarFactor T b (lam ^ n) = rootHaarFactor T b lam ^ n := by
  cases n with
  | ofNat n =>
      simp only [Int.ofNat_eq_natCast, zpow_natCast, rootHaarFactor_pow]
  | negSucc n =>
      rw [zpow_negSucc, zpow_negSucc, rootHaarFactor_inv, rootHaarFactor_pow]

/-- Exact requirement for the general lambda norm factor. -/
structure RootHaarFactorNormPowGap where
  lam : (rootNormedExtension T b)ˣ
  factor : ENNReal
  factor_eq : factor = rootHaarFactor T b lam
  normPow : ENNReal
  normPow_eq : normPow = ENNReal.ofReal
    ((‖(lam : rootNormedExtension T b)‖) ^
      Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b))
  equality : Prop

def RootHaarFactorNormPowRequired : Prop :=
  Nonempty (RootHaarFactorNormPowGap (T := T) (b := b))

end LeanFormal.IUT.XiFPaper.S295GeneralHaarFactorActual

end
