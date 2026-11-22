import tmp.sheaf.xif.paper.Mzk1CarrierBadInvScaleProductActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# shehdd A664 carrier scaling LOG law (Sha, read-only)

Carrier-level scaling log law: the `s1902NormalizedHaar` measure is a scalar
multiple `s1902HaarScale • rootExtensionProductHaar`, so the REAL log of a region
volume splits as `log scale + log product-volume`.  Combined with the green
`badInvScale_productHaar_pi` rectangle product law this gives the additive
log lever of the inverse bad-prime scaling (the core of the mainline
`CarrierScalingLogLaw`), conditional on the explicit positivity/finiteness
conditions.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1CarrierScalingLogLawShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleProductActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Real log of the scalar-multiplied measure value splits additively. -/
theorem real_log_smul_measure_apply
    (c : ENNReal) (mu : Measure (S1902Carrier T)) (S : Set (S1902Carrier T))
    (hc0 : c ≠ 0) (hcT : c ≠ ⊤)
    (hS0 : mu S ≠ 0) (hST : mu S ≠ ⊤) :
    Real.log (((c • mu) S).toReal) =
      Real.log c.toReal + Real.log (mu S).toReal := by
  have hsm : ((c • mu) S) = c * mu S := by
    rw [Measure.smul_apply, smul_eq_mul]
  rw [hsm, ENNReal.toReal_mul, Real.log_mul
    (ENNReal.toReal_ne_zero.mpr ⟨hc0, hcT⟩)
    (ENNReal.toReal_ne_zero.mpr ⟨hS0, hST⟩)]

/-- The `s1902NormalizedHaar` log splits into `log s1902HaarScale + log product`. -/
theorem s1902_log_split (S : Set (S1902Carrier T))
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T ≠ ⊤)
    (hS0 : rootExtensionProductHaar T S ≠ 0)
    (hST : rootExtensionProductHaar T S ≠ ⊤) :
    Real.log ((s1902NormalizedHaar T S).toReal) =
      Real.log (s1902HaarScale T).toReal +
        Real.log ((rootExtensionProductHaar T S).toReal) := by
  unfold s1902NormalizedHaar
  exact real_log_smul_measure_apply T (s1902HaarScale T) (rootExtensionProductHaar T) S
    hc0 hcT hS0 hST

structure CarrierLogRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def carrierLogRows : List CarrierLogRow :=
  [ ⟨"real log split", "log((c smul mu) S).toReal = log c.toReal + log (mu S).toReal", "GREEN_CONDITIONAL"⟩
  , ⟨"s1902 log split", "s1902NormalizedHaar = s1902HaarScale smul productHaar", "GREEN_CONDITIONAL"⟩
  , ⟨"badInvScale product law", "badInvScale_productHaar_pi (mainline green)", "GREEN_SOURCE"⟩
  , ⟨"normalized/truncation", "s1902LogVolume uses ofReal(log) truncation; handled separately", "NEXT_STEP"⟩
  , ⟨"scope", "log law only; no gap claimed", "INTEGRITY"⟩
  ]

theorem carrierLogRows_length : carrierLogRows.length = 5 := rfl

theorem carrierLogRows_statuses_ok :
    carrierLogRows.all (fun r =>
      r.status ∈ ["GREEN_CONDITIONAL", "GREEN_SOURCE", "NEXT_STEP", "INTEGRITY"]) = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1CarrierScalingLogLawShaActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1CarrierScalingLogLawShaActual.real_log_smul_measure_apply
#print axioms LeanFormal.IUT.XiFPaper.Mzk1CarrierScalingLogLawShaActual.s1902_log_split
