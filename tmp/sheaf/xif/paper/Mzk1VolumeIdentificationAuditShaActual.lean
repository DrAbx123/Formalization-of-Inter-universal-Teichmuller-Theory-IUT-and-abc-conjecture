import tmp.sheaf.xif.paper.Mzk1ScaledClosingShaActual
import tmp.sheaf.xif.paper.Mzk1QSideExplicitActual
import tmp.sheaf.xif.paper.Mzk1HullLogVolumeFormulaActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import Mathlib.Tactic

/-!
# A811 volume identification audit (shehdd)

Collects the green identifications between our volume objects (needed by the final
boundary certificate V3's OPEN item "paper normalization bridge to lana logVol"):

1. RAW scaled volume: `rootExtensionProductHaar (scaledThetaHull k) =
   (∏_b rootPrimeHaarFactor_b^k) * rootExtensionProductHaar fullRegion`;
2. RAW log scaling: `log(raw scaled) = log(raw full) - k·Σ_b d_b log p_b`;
3. NORMALIZED log scaling: `rootExtensionProductNormalizedLog (scaledThetaHull k) =
   scaledClosedFormR k - 1` (S1902 `+1` correction);
4. full-region log-volume: `s1902LogVolume fullRegion = ofReal (s1915ClosedForm)`;
5. q side: `qSideContribution P = -qPilotLogVolumeReading P = A` and
   `qPilotLogVolumeReading P = -order·log(residueNormBase)`;
6. VPaper: `VPaper T P k = scaledClosedFormR k - 1 + qSideContribution`;
7. scaled statement: `ScaledPaper312Statement ↔ qSideContribution ≥ 1 - scaledClosedFormR`.

Still OPEN (pointer for boundary V3): identification with lana `logVol`/`VcI`
(`Iut/Wall/Rss.lean:323-324`, `Iut/WallEquiv/VcI.lean:740+`): needs archimedean
(`VcI.lean:657,700`), procession average `1/nC`, c_lana = `(sFactor-1)/(2ℓ)`, and A763
c_V bookkeeping.  Recorded, not assumed.

No RETRACTED statement is used.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1VolumeIdentificationAuditShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1ScaledClosingShaActual
open LeanFormal.IUT.XiFPaper.Mzk1VPaperActual
open LeanFormal.IUT.XiFPaper.Mzk1ScaledPaper312Actual
open LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullScalingShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullNormalizedLogShaActual
open LeanFormal.IUT.XiFPaper.Mzk1QSideExplicitActual
open LeanFormal.IUT.XiFPaper.Mzk1HullLogVolumeFormulaActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeScalingActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarProductStrictMainlineActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- 1. Raw scaled volume identification (iterated Haar scaling law). -/
theorem volume_raw_scaling (k : ℕ) :
    rootExtensionProductHaar T (scaledThetaHull T k) =
      (∏ b : Bad (nativePlaceSelection T), (rootPrimeHaarFactor T b) ^ k) *
        rootExtensionProductHaar T (fullRegion T) :=
  scaledThetaHull_measure_eq T k

/-- 2. Raw log scaling. -/
theorem volume_raw_log_scaling (k : ℕ) :
    Real.log ((rootExtensionProductHaar T (scaledThetaHull T k)).toReal) =
      Real.log ((rootExtensionProductHaar T (fullRegion T)).toReal) -
        (k : ℝ) * qLogSum T :=
  scaledThetaHull_log_toReal T k

/-- 3. Normalized log scaling with the S1902 `+1` correction. -/
theorem volume_normalized_scaling (k : ℕ) :
    rootExtensionProductNormalizedLog T (scaledThetaHull T k) =
      scaledClosedFormR T k - 1 :=
  scaledThetaHull_normalizedLog_eq T k

/-- 4. Full-region log-volume in the S1915 closed form. -/
theorem volume_full_eq_s1915 :
    s1902LogVolume T (fullRegion T) =
      ENNReal.ofReal (s1915ClosedForm T) := by
  have h := s1915_logVolume_eq T
  rwa [← fullRegion_eq_hull T] at h

variable {V2 : Type} {I2 : OriginalInput l V2}
variable (P : PaperQPilotObjectActual (l := l) (I := I2))

/-- 5a. q side: `qSideContribution = -qPilotLogVolumeReading = A`. -/
theorem volume_qSide_identification :
    qSideContribution P = -qPilotLogVolumeReading P :=
  qSideContribution_eq_neg_reading P

/-- 5b. q reading: `log ‖q‖` (closed form; = `-|log q|`). -/
theorem volume_qReading_log_norm :
    qPilotLogVolumeReading P = Real.log ‖P.line.C3.q.q‖ :=
  qPilotLogVolumeReading_eq_log_norm P

/-- 6. `VPaper` in volume-identification coordinates. -/
theorem volume_VPaper_closed_form (k : ℕ) :
    VPaper T P k = scaledClosedFormR T k - 1 + qSideContribution P :=
  VPaper_eq_closedForm T P k

/-- 7. Scaled statement in closed-form coordinates. -/
theorem volume_scaledStatement_iff (k : ℕ) :
    Mzk1ScaledPaper312Actual.ScaledPaper312Statement T
        (qPilotLogVolumeReading P) k ↔
      qSideContribution P ≥ 1 - scaledClosedFormR T k :=
  scaledPaper312_iff_closedForm T P k

structure VolumeIdRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def volumeIdRows : List VolumeIdRow :=
  [ ⟨"raw scaling", "productHaar(scaledThetaHull k) = (∏ primeFactor^k)*productHaar full", "PROVED"⟩
  , ⟨"raw log scaling", "log raw scaled = log raw full - k*qLogSum", "PROVED"⟩
  , ⟨"normalized scaling", "normalizedLog scaled = scaledClosedFormR k - 1", "PROVED"⟩
  , ⟨"full-region volume", "s1902LogVolume full = ofReal(s1915ClosedForm)", "PROVED"⟩
  , ⟨"q side", "qSideContribution = -qReading = order*log residueNormBase", "PROVED"⟩
  , ⟨"VPaper", "VPaper = scaledClosedFormR k - 1 + qSideContribution", "PROVED"⟩
  , ⟨"scaled statement", "statement <-> qSide >= 1 - scaledClosedFormR k", "PROVED"⟩
  , ⟨"lana logVol bridge", "logVol = procession average (1/nC); VcI hull packet; archimedean log(sqrt2*pi)", "OPEN (V3 pointer)"⟩
  , ⟨"c_lana", "(sFactor-1)/(2l) <-> c_V=1/4 bookkeeping", "PENDING"⟩
  , ⟨"scope", "internal identifications only; no RETRACTED use", "INTEGRITY"⟩
  ]

theorem volumeIdRows_length : volumeIdRows.length = 10 := rfl

theorem volumeIdRows_has_open :
    volumeIdRows.any (fun r => r.status = "OPEN (V3 pointer)") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1VolumeIdentificationAuditShaActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1VolumeIdentificationAuditShaActual.volume_raw_scaling
#print axioms LeanFormal.IUT.XiFPaper.Mzk1VolumeIdentificationAuditShaActual.volume_normalized_scaling
#print axioms LeanFormal.IUT.XiFPaper.Mzk1VolumeIdentificationAuditShaActual.volume_full_eq_s1915
#print axioms LeanFormal.IUT.XiFPaper.Mzk1VolumeIdentificationAuditShaActual.volume_VPaper_closed_form
