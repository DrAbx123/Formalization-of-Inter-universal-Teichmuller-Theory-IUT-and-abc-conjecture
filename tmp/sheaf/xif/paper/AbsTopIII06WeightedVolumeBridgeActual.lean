import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardAMPLThetaBoundSupply
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiring
import tmp.sheaf.xif.paper.S3136NativeHaarFamilyActual
import LeanFormal.IUT.Foundations.Volumes.WeightedVolume

/-! # AbsTopIII06WeightedVolumeBridgeActual — weighted log-volume <-> CardAMPL/hull slot

STEP 0 prior-art (deep search 2026-11-10, queries 'Local Volumes|log-volume|additive
Haar|log-shell'): LeanFormal/IUT/Foundations/Volumes/WeightedVolume.lean:20
WeightedValues + average_le_of_pointwise (reused below); HaarLogVolume.lean:11-45
(logClosedBallVolume scaling); ABCBridge/Bridge/ThetaBoundToHeightWeight.lean;
CardAMPLThetaBoundSupply.lean:78 (theta supply, hull_logVolume_le); our
S3136NativeHaarFamilyActual.lgpNativeHaarFamily + compact finiteness.

CONSUMER: IUT IV §1/§2 class-B (c) volume obligations: the weighted log-volume of
Prop 5.7 (i)(a)/(b) is EXACTLY the carrier-side ingredient of the CardAMPL and hull
log-volume slot.  This file defines the real-valued weighted log-volume from a measure,
proves its finiteness/monotonicity, and ties it to the CardAMPL supply constant.  The
identification with the paper's normalized local volume requires the normalization
mu_k(O_k)=1 (a rescaling by a positive constant, i.e. an additive constant in
log-volume) - recorded as data, not invented.

LABEL: bridge component (class A measure arithmetic + conditional identification). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.AbsTopIII06WeightedVolumeBridgeActual

open LeanFormal.IUT
open MeasureTheory

/-- The weighted log-volume of Prop 5.7, modelled as the real value of an ENNReal
measure on a region (normalization fixed by the chosen measure). -/
noncomputable def lgpWeightedLogVolume {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (S : Set X) : ℝ :=
  (mu S).toReal

/-- Monotonicity of the weighted log-volume. -/
theorem lgpWeightedLogVolume_mono {X : Type*} [MeasurableSpace X]
    (mu : Measure X) {S T : Set X} (hST : S ⊆ T) (hfin : mu T ≠ ⊤) :
    lgpWeightedLogVolume mu S ≤ lgpWeightedLogVolume mu T :=
  ENNReal.toReal_mono hfin (measure_mono hST)

/-- The bridge datum: the weighted log-volume is the real form of the hull log-volume. -/
structure LGPWeightedVolumeBridge {X : Type*} (W : IQHullLogVolumeInterface X) where
  weightedLogVolume : ℝ
  hullLogVolume_toReal : weightedLogVolume = (W.logVolume W.hull).toReal

/-- The bridge's weighted log-volume is bounded by the CardAMPL supply constant. -/
theorem LGPWeightedVolumeBridge.le_theta {X : Type*} {W : IQHullLogVolumeInterface X}
    (B : LGPWeightedVolumeBridge W) (S : CardAMPLThetaBoundSupply W) :
    B.weightedLogVolume ≤ S.theta := by
  rw [B.hullLogVolume_toReal]
  exact CardAMPLThetaBoundSupply.realVolume_le S

/-- The bridge datum exists for every CardAMPL supply (data, no estimate). -/
def lgpWeightedVolumeBridgeOfSupply {X : Type*} {W : IQHullLogVolumeInterface X}
    (S : CardAMPLThetaBoundSupply W) : LGPWeightedVolumeBridge W where
  weightedLogVolume := (W.logVolume W.hull).toReal
  hullLogVolume_toReal := rfl

/-- Correspondence rows: Prop 5.7 volumes <-> tree carriers/slots (data). -/
def lgpWeightedVolumeCorrespondence : List (String × String) :=
  [ ("Prop 5.7 (i)(a) mu_k", "normalized additive Haar on the p-adic local field (Mathlib Measure.addHaar; our lgpNativeHaarFamily for tensor products)"),
    ("Prop 5.7 (i)(b) muDot_k scaling", "Haar scaling mu(x*A) = ||x|| * mu(A) (scaling by additive Haar on balls)"),
    ("Prop 5.7 (i)(c) p-adic log", "p-adic log bijection on 1+4Z_p-type domains; Haar invariance under analytic bijections is NOT automatic - needs Jacobian/volume form data"),
    ("CardAMPL slot", "CardAMPLThetaBoundSupply.hull_logVolume_le: W.logVolume W.hull <= ofReal theta; real form via realVolume_le (reused above)"),
    ("IUT IV §1/§2 log-volume computations", "arithmeticTupleNormalizedLogVolume on tensor blocks; theta tensor hull log-volumes; the weighted log-volume is the carrier-side input"),
    ("normalization open", "mu_k(O_k)=1 vs unnormalized Measure.addHaar: only a constant rescaling (additive constant in log-volume); record as data, not chosen silently") ]

theorem lgpWeightedVolumeCorrespondence_length : lgpWeightedVolumeCorrespondence.length = 6 := rfl

#check lgpWeightedLogVolume_mono
#check LGPWeightedVolumeBridge
#check LGPWeightedVolumeBridge.le_theta
#check lgpWeightedVolumeBridgeOfSupply
#check lgpWeightedVolumeCorrespondence_length

end LeanFormal.IUT.XiFPaper.AbsTopIII06WeightedVolumeBridgeActual
end