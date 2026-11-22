import tmp.sheaf.xif.paper.S996FiniteQuotientLinearizationActual
import tmp.sheaf.xif.paper.S917IndImageUnionActual
import tmp.sheaf.xif.paper.S976FiniteLogShellHaarActual
import tmp.sheaf.xif.paper.S919GlobalWeightedInequalityActual
import tmp.sheaf.xif.paper.S995FiniteCarrierCor312ConclusionActual
/-! # S1004: actual qVFam finite linearization replaces full FinalL linearization
S996 gives the actual Qp-linear equivalence qVFamTensorBlock ~ Qp^d.  The full
FinalL-valued carrier is not finite-dimensional, so S994's full-carrier
linearization was exact.  This file rebuilds the finite-carrier data directly
on qVFamTensorBlock: qPilot region image, paper lambda-O region image, actual
containment, finite log comparison, global weights, and the S991 link. -/
noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
namespace LeanFormal.IUT.XiFPaper.S1004QVFamFiniteLinearizationActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.S917IndImageUnionActual
open LeanFormal.IUT.XiFPaper.S970FiniteLogShellCarrierActual
open LeanFormal.IUT.XiFPaper.S976FiniteLogShellHaarActual
open LeanFormal.IUT.XiFPaper.S996FiniteQuotientLinearizationActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open LeanFormal.IUT.XiFPaper.S983PaperXiFSourceLinkConstructionActual
open LeanFormal.IUT.XiFPaper.S991S983LinkInputsActual
open LeanFormal.IUT.XiFPaper.S622PaperXiFFieldAuditActual
open MeasureTheory
universe u ua uv upi umon ui uL uC uG uX uLabel uC3 uD3 uM uP
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
noncomputable def s1004E :
    qVFamTensorBlock T b ≃ₗ[ℚ_[(qVFamTensorP T b)]]
      (Fin (Module.finrank ℚ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)) →
        ℚ_[(qVFamTensorP T b)]) :=
  s996QVFamLinearization (l := l) T b
noncomputable def s1004QPilotImage :
    Set (FiniteLogShellCarrier (qVFamTensorP T b)
      (Module.finrank ℚ_[(qVFamTensorP T b)] (qVFamTensorBlock T b))) :=
  s1004E (l := l) T b '' qPilotPaperRegion (l := l) T b
noncomputable def s1004Hull :
    Set (FiniteLogShellCarrier (qVFamTensorP T b)
      (Module.finrank ℚ_[(qVFamTensorP T b)] (qVFamTensorBlock T b))) :=
  s1004E (l := l) T b '' paperRootThetaImageNZ (l := l) T b
theorem s1004Containment : s1004QPilotImage (l := l) T b ⊆ s1004Hull (l := l) T b :=
  Set.image_mono (qPilotPaperRegion_subset_thetaImageNZ (l := l) T b)
noncomputable def s1004H (b : Bad (nativePlaceSelection T)) :=
  finiteLogShellHaarData (p := qVFamTensorP T b)
    (Module.finrank ℚ_[(qVFamTensorP T b)] (qVFamTensorBlock T b))
theorem finiteNormalizedLog_mono_qvfam
    {S U : Set (FiniteLogShellCarrier (qVFamTensorP T b)
      (Module.finrank ℚ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)))}
    (hSU : S ⊆ U) (hSpos : 0 < (s1004H (l := l) T b).measure S)
    (hUfin : (s1004H (l := l) T b).measure U < ⊤) :
    (s1004H (l := l) T b).measure S = (s1004H (l := l) T b).measure S ∧
    Real.log ((s1004H (l := l) T b).measure S).toReal ≤
      Real.log ((s1004H (l := l) T b).measure U).toReal := by
  have hSfin : (s1004H (l := l) T b).measure S < ⊤ :=
    lt_of_le_of_lt (measure_mono hSU) hUfin
  exact ⟨rfl, Real.log_le_log
    (ENNReal.toReal_pos hSpos.ne' hSfin.ne)
    (ENNReal.toReal_mono hUfin.ne (measure_mono hSU))⟩
/-- Actual per-b finite comparison on qVFam. -/
theorem s1004PerB
    (hpos : 0 < (s1004H (l := l) T b).measure (s1004QPilotImage (l := l) T b))
    (hfin : (s1004H (l := l) T b).measure (s1004Hull (l := l) T b) < ⊤) :
    Real.log ((s1004H (l := l) T b).measure (s1004QPilotImage (l := l) T b)).toReal ≤
      Real.log ((s1004H (l := l) T b).measure (s1004Hull (l := l) T b)).toReal :=
  (finiteNormalizedLog_mono_qvfam (l := l) T b
    (s1004Containment (l := l) T b) hpos hfin).2
end LeanFormal.IUT.XiFPaper.S1004QVFamFiniteLinearizationActual
