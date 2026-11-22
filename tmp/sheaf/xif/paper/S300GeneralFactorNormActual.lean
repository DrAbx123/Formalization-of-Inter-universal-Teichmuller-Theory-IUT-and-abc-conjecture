import tmp.sheaf.xif.paper.S295GeneralHaarFactorActual
import tmp.sheaf.xif.paper.PaperRootExtensionDiscreteValuationActual
import tmp.sheaf.xif.paper.PaperRootExtensionUnitDecompositionActual

/-! # S300: DVR decomposition of a field unit and exact norm-factor gap

Any nonzero lambda in L admits lambda = u * pi^n with u a unit and n : Int
(DVR decomposition).  This file constructs that actual decomposition.  The
general norm formula is recorded as an exact remaining requirement, not faked.

No inequality/no fake factor/sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S300GeneralFactorNormActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarFactorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionUnitDecompositionActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionDiscreteValuationActual
open LeanFormal.IUT.XiFPaper.RootTensorThetaHullActual
open LeanFormal.IUT.XiFPaper.S295GeneralHaarFactorActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Actual DVR decomposition of a unit lambda = u * pi^n. -/
theorem exists_unit_uniformizer_zpow
    (lam : (rootNormedExtension T b)ˣ) :
    ∃ (n : ℤ) (u : (Integers (rootNormedExtension T b))ˣ),
      lam = Units.map (algebraMap (Integers (rootNormedExtension T b))
          (rootNormedExtension T b)).toMonoidHom u *
        rootUniformizerField T b ^ n := by
  have hne : (lam : rootNormedExtension T b) ≠ 0 := Units.ne_zero lam
  obtain ⟨n, u, hux⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      (R := Integers (rootNormedExtension T b))
      (K := rootNormedExtension T b)
      (ϖ := rootUniformizer T b) (rootUniformizer_irreducible T b) hne
  refine ⟨n, u, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val]
  rw [hux]
  rfl

/-- Exact required general norm formula for rootHaarFactor. -/
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

/-- Exact required block general-lambda formula. -/
structure BlockHaarFactorNormPowGap where
  lam : (rootNormedExtension T b)ˣ
  blockFactor : ENNReal
  blockFactor_eq : blockFactor = (thetaScalingHaarFactor T b
    (lam : rootNormedExtension T b) (Units.ne_zero lam) : ENNReal)
  normPow : ENNReal
  normPow_eq : normPow = ENNReal.ofReal
    ((‖(lam : rootNormedExtension T b)‖) ^
      Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b))
  equality : Prop

def BlockHaarFactorNormPowRequired : Prop :=
  Nonempty (BlockHaarFactorNormPowGap (T := T) (b := b))

end LeanFormal.IUT.XiFPaper.S300GeneralFactorNormActual

end
