import tmp.sheaf.xif.paper.S996FiniteQuotientLinearizationActual
import tmp.sheaf.xif.paper.S917IndImageUnionActual
import tmp.sheaf.xif.paper.S976FiniteLogShellHaarActual
import tmp.sheaf.xif.paper.S919GlobalWeightedInequalityActual
import tmp.sheaf.xif.paper.S991S983LinkInputsActual
/-! # S994 (S1004 revision): finite qVFam linearization
S996 gives the actual finite qVFam linearization; the full FinalL carrier is
not finite-dimensional.  All per-b finite data are now on qVFamTensorBlock
transported to Fin d -> Qp, with actual containment.  Only positivity,
finiteness and the source link remain as conditions. -/
noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
namespace LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
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
/-- Actual finite linearization of qVFamTensorBlock. -/
structure S994FiniteLinearization where
  d : Nat
  e : qVFamTensorBlock T b ≃ₗ[ℚ_[(qVFamTensorP T b)]]
    (Fin d → ℚ_[(qVFamTensorP T b)])
noncomputable def s994ActualLinearization : S994FiniteLinearization T b where
  d := Module.finrank ℚ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)
  e := s996QVFamLinearization (l := l) T b
noncomputable def s994H (L : S994FiniteLinearization T b) :=
  finiteLogShellHaarData (p := qVFamTensorP T b) L.d
noncomputable def s994QPilotImage (L : S994FiniteLinearization T b) :
    Set (FiniteLogShellCarrier (qVFamTensorP T b) L.d) :=
  L.e '' qPilotPaperRegion (l := l) T b
noncomputable def s994Hull (L : S994FiniteLinearization T b) :
    Set (FiniteLogShellCarrier (qVFamTensorP T b) L.d) :=
  L.e '' paperRootThetaImageNZ (l := l) T b
theorem s994Containment (L : S994FiniteLinearization T b) :
    s994QPilotImage (l := l) T b L ⊆ s994Hull (l := l) T b L :=
  Set.image_mono (qPilotPaperRegion_subset_thetaImageNZ (l := l) T b)
structure S994PerBInput where
  linearization : S994FiniteLinearization T b
  qPilot_pos : 0 < (s994H (l := l) T b linearization).measure
    (s994QPilotImage (l := l) T b linearization)
  hull_finite : (s994H (l := l) T b linearization).measure
    (s994Hull (l := l) T b linearization) < ⊤
theorem s994PerBLogComparison (I : S994PerBInput T b) :
    (s994H (l := l) T b I.linearization).measure
        (s994QPilotImage (l := l) T b I.linearization) < ⊤ ∧
      Real.log ((s994H (l := l) T b I.linearization).measure
        (s994QPilotImage (l := l) T b I.linearization)).toReal ≤
      Real.log ((s994H (l := l) T b I.linearization).measure
        (s994Hull (l := l) T b I.linearization)).toReal := by
  have hSfin : (s994H (l := l) T b I.linearization).measure
      (s994QPilotImage (l := l) T b I.linearization) < ⊤ :=
    lt_of_le_of_lt (measure_mono (s994Containment (l := l) T b I.linearization))
      I.hull_finite
  exact ⟨hSfin, Real.log_le_log
    (ENNReal.toReal_pos I.qPilot_pos.ne' hSfin.ne)
    (ENNReal.toReal_mono I.hull_finite.ne
      (measure_mono (s994Containment (l := l) T b I.linearization)))⟩
structure S994FiniteInput where
  L : (b : Bad (nativePlaceSelection T)) → S994FiniteLinearization T b
  qPilot_pos : ∀ b, 0 < (s994H (l := l) T b (L b)).measure
    (s994QPilotImage (l := l) T b (L b))
  hull_finite : ∀ b, (s994H (l := l) T b (L b)).measure
    (s994Hull (l := l) T b (L b)) < ⊤
noncomputable def s994VR (In : S994FiniteInput T) (b : Bad (nativePlaceSelection T)) : Real :=
  Real.log ((s994H (l := l) T b (In.L b)).measure
    (s994QPilotImage (l := l) T b (In.L b))).toReal
noncomputable def s994VS (In : S994FiniteInput T) (b : Bad (nativePlaceSelection T)) : Real :=
  Real.log ((s994H (l := l) T b (In.L b)).measure
    (s994Hull (l := l) T b (In.L b))).toReal
theorem s994GlobalWeightedInequality (In : S994FiniteInput T) :
    weightedPaperV T (s994VR T In) ≤ weightedPaperV T (s994VS T In) := by
  apply weightedPaperV_mono T
  intro b
  exact (s994PerBLogComparison T b
    { linearization := In.L b
      qPilot_pos := In.qPilot_pos b
      hull_finite := In.hull_finite b }).2
end LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
