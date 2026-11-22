import tmp.sheaf.xif.paper.S865RootHaarFactorNormPowActual
import Mathlib.Tactic
/-! Principal-region normalized scalar readout.

For a nonzero root-extension element `lam`, the Haar factor is `||lam||^d`, so the
dimension-normalized log mass of the principal region `lam * O` is exactly `log ||lam||`.
This is the concrete scalar readout used in doc §8.3; no carrier equality is asserted. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1BoxPrincipalScalarActual
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarFactorActual
open LeanFormal.IUT.XiFPaper.S865RootHaarFactorNormPowActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
/-- The actual dimension of the root-normed extension at the bad place. -/
def principalDim (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Nat :=
  Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
/-- Principal-region normalized scalar readout: log mass divided by the actual dimension
equals the signed log norm. -/
theorem principal_region_normalized_scalar
    (hd : principalDim T b ≠ 0)
    (lam : (rootNormedExtension T b)ˣ) :
    Real.log
        (((rootHaarFactor T b lam).toReal)) / (principalDim T b : Real) =
      Real.log ‖((lam : (rootNormedExtension T b)))‖ := by
  have hfac := rootHaarFactor_normPow_actual (l := l) T b lam
  have hto : (rootHaarFactor T b lam).toReal =
      (‖((lam : (rootNormedExtension T b)))‖) ^ principalDim T b := by
    rw [hfac, ENNReal.toReal_ofReal (by positivity), principalDim]
  have hd' : (principalDim T b : Real) ≠ 0 := by
    exact_mod_cast hd
  rw [hto, Real.log_pow]
  field_simp [hd']
end LeanFormal.IUT.XiFPaper.Mzk1BoxPrincipalScalarActual
end
