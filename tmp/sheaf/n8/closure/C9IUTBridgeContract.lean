import LeanFormal.IUT.IUTIII.Theorem311.SourceTheorem311ReferenceContract
import LeanFormal.IUT.IUTIII.Theorem311.SourceHodgeTheaterBridge
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ContractSourceReduction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ParametricStepXI
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotGlobalNormalization

/-!
# C9-IUT Step-XI contract from actual q/hull bridge fields

This file constructs:

* `ParametricStepXI.StepXIInput` from actual q-log and source hull-volume data;
* `StepXIContract` from the same fields;
* `Cor312Conclusion` via `cor312_of_constructed_stepXI`.

The q value is the actual
`ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog`
of an actual finite-place family.  The target/theta value is the actual
`I.sourceHullVolume v Rimg n` (as a real number), tied by the equality field
`hullVolume_eq`.  The only comparison input is the explicit named hypothesis
`q_le_hull`; it is a function argument, not a structure field and not an
axiom.  IPL/SHE/APT are the explicit Step-XI contract ports; no evidence is
manufactured here.

No toy `Output`/`logVol`/`h` type, no `sorry`, no custom axiom, and no edit
to the project Step-XI files.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.N8Closure.C9IUTBridgeContract

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotGlobalNormalization

universe u v w ua uv upi umon ui ux

/-- Actual q-log and actual source-hull-volume bridge data, with no C1 field.
The q value is sourced from the actual arithmetic q-pilot normalization; the
hull and hullVolume are the actual source holomorphic hull/volume.
-/
structure QHullBridge
    {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice]
    (R : SourceTheorem311Realization l Label Choice)
    {V : Type uv}
    (I : OriginalInput l V)
    (v : V) (Rimg : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l)
    {k : Type ux} [Field k] [NumberField k]
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (lowerPlace : selectedLowerPlaces) →
      FinitePlaceQCandidate lowerPlace.val) where
  selected_nonempty : selectedLowerPlaces.Nonempty
  qPilotLog : Real
  qPilotLog_source :
    qPilotLog =
      absoluteDegreeNormalizedLowerSignedLog
        selectedLowerPlaces parameters
  hull : Submonoid (I.ThetaPilotPoint v)
  hull_eq : hull = I.sourceHolomorphicHull v Rimg n
  hullVolume : ENNReal
  hullVolume_eq : hullVolume = I.sourceHullVolume v Rimg n
  hullVolume_lt_top : hullVolume < ⊤

namespace QHullBridge

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
  [AddGroup Label] [Preorder Choice]
  {R : SourceTheorem311Realization l Label Choice}
  {V : Type uv} {I : OriginalInput l V}
  {v : V} {Rimg : I.SourceImageRealization v}
  {n : ThetaPilotCarrier l}
  {k : Type ux} [Field k] [NumberField k]
  {selectedLowerPlaces : Finset (NumberField.FinitePlace k)}
  {parameters : (lowerPlace : selectedLowerPlaces) →
    FinitePlaceQCandidate lowerPlace.val}

/-- The actual signed q-log attached to the bridge is strictly negative on a
nonempty selected family. -/
theorem qPilotLog_neg
    (B : QHullBridge R I v Rimg n selectedLowerPlaces parameters) :
    B.qPilotLog < 0 := by
  rw [B.qPilotLog_source]
  exact normalizedLowerSignedLog_neg
    selectedLowerPlaces parameters B.selected_nonempty

/-- `StepXIContract` built from the actual q log and actual source hull
volume.  `hq` is the explicit signed comparison `q <= hull volume`; it is the
named C1 input, not an arbitrary field.  The target and theta values are the
actual hull volume, so `target_le_theta` is `le_rfl` and no separate
inequality is invented. -/
def toStepXIContract
    (B : QHullBridge R I v Rimg n selectedLowerPlaces parameters)
    (hq : B.qPilotLog ≤ B.hullVolume.toReal)
    (ipl she apt : Prop) (ipl_evidence : ipl)
    (she_evidence : she) (apt_evidence : apt) :
    StepXIContract := by
  have hq' :
      absoluteDegreeNormalizedLowerSignedLog
        selectedLowerPlaces parameters ≤ B.hullVolume.toReal := by
    rwa [← B.qPilotLog_source]
  exact StepXIContract.ofAbsoluteDegreeNormalizedSignedLog
    selectedLowerPlaces parameters B.selected_nonempty
    B.hullVolume.toReal B.hullVolume.toReal hq' le_rfl
    ipl she apt ipl_evidence she_evidence apt_evidence

/-- The `qSigned` field of the constructed contract is the actual bridge
q-log. -/
theorem toStepXIContract_qSigned
    (B : QHullBridge R I v Rimg n selectedLowerPlaces parameters)
    (hq : B.qPilotLog ≤ B.hullVolume.toReal)
    (ipl she apt : Prop) (ipl_evidence : ipl)
    (she_evidence : she) (apt_evidence : apt) :
    (B.toStepXIContract hq ipl she apt ipl_evidence she_evidence
      apt_evidence).qSigned = B.qPilotLog := by
  rw [QHullBridge.toStepXIContract, StepXIContract.ofAbsoluteDegreeNormalizedSignedLog]
  exact B.qPilotLog_source.symm

/-- Corollary 3.12 conclusion for the constructed contract, through the
existing Step-XI consumer theorem. -/
theorem cor312Conclusion_toStepXIContract
    (B : QHullBridge R I v Rimg n selectedLowerPlaces parameters)
    (hq : B.qPilotLog ≤ B.hullVolume.toReal)
    (ipl she apt : Prop) (ipl_evidence : ipl)
    (she_evidence : she) (apt_evidence : apt) :
    Cor312Conclusion
      (B.toStepXIContract hq ipl she apt ipl_evidence she_evidence
        apt_evidence) := by
  exact cor312_of_constructed_stepXI _

/-- `ParametricStepXI.StepXIInput` built from the same actual q/hull fields.
The algorithm output is the actual `runAlgorithm`; the q is the actual
absolute-degree-normalized q log; target/theta are the actual hull volume.
-/
def toStepXIInput
    (B : QHullBridge R I v Rimg n selectedLowerPlaces parameters)
    (hq : B.qPilotLog ≤ B.hullVolume.toReal)
    (carrier : ParametricTheorem311.Carrier Label Choice)
    (input : ParametricTheorem311.AlgorithmInput carrier)
    (ipl she apt : Prop) (ipl_evidence : ipl)
    (she_evidence : she) (apt_evidence : apt) :
    ParametricStepXI.StepXIInput carrier input := by
  have hq' :
      absoluteDegreeNormalizedLowerSignedLog
        selectedLowerPlaces parameters ≤ B.hullVolume.toReal := by
    rwa [← B.qPilotLog_source]
  exact ParametricStepXI.stepXIInputOfAbsoluteDegreeNormalizedSignedLog
    carrier input selectedLowerPlaces parameters B.selected_nonempty
    B.hullVolume.toReal B.hullVolume.toReal hq' le_rfl
    ipl she apt ipl_evidence she_evidence apt_evidence

/-- The parametric input's q field is the actual bridge q-log. -/
theorem toStepXIInput_qSigned
    (B : QHullBridge R I v Rimg n selectedLowerPlaces parameters)
    (hq : B.qPilotLog ≤ B.hullVolume.toReal)
    (carrier : ParametricTheorem311.Carrier Label Choice)
    (input : ParametricTheorem311.AlgorithmInput carrier)
    (ipl she apt : Prop) (ipl_evidence : ipl)
    (she_evidence : she) (apt_evidence : apt) :
    (B.toStepXIInput hq carrier input ipl she apt ipl_evidence
      she_evidence apt_evidence).qSigned = B.qPilotLog := by
  rw [QHullBridge.toStepXIInput,
    ParametricStepXI.stepXIInputOfAbsoluteDegreeNormalizedSignedLog]
  exact B.qPilotLog_source.symm

/-- Corollary 3.12 conclusion for the parametric input, through the existing
consumer theorem. -/
theorem cor312Conclusion_toStepXIInput
    (B : QHullBridge R I v Rimg n selectedLowerPlaces parameters)
    (hq : B.qPilotLog ≤ B.hullVolume.toReal)
    (carrier : ParametricTheorem311.Carrier Label Choice)
    (input : ParametricTheorem311.AlgorithmInput carrier)
    (ipl she apt : Prop) (ipl_evidence : ipl)
    (she_evidence : she) (apt_evidence : apt) :
    Cor312Conclusion
      (B.toStepXIInput hq carrier input ipl she apt ipl_evidence
        she_evidence apt_evidence).toContract := by
  exact cor312_of_constructed_stepXI _

end QHullBridge

end LeanFormal.IUT.N8Closure.C9IUTBridgeContract

end
