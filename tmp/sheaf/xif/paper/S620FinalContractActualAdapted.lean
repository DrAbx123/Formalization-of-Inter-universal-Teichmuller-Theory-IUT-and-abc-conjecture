import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealSignedLogVolume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ConcreteFiniteRouteColumns
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealGeometryReduction

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S620FinalContractActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.ArithmeticQPilotGlobalNormalization

universe ua uv upi umon ui uK

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable {k : Type uK} [Field k] [NumberField k]
variable (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
variable (parameters : (lowerPlace : selectedLowerPlaces) →
  NumberFieldFinitePlace.FinitePlaceQCandidate lowerPlace.val)
variable (selected_nonempty : selectedLowerPlaces.Nonempty)

/-- Actual qSigned: absolute-degree-normalized lower signed q-log. -/
noncomputable def sourceQSigned : Real :=
  ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
    selectedLowerPlaces parameters

/-- Actual target: source signed hull log-volume. -/
noncomputable def sourceTargetSigned : Real :=
  I.sourceSignedHullLogVolume v R n

/-- Actual thetaSigned: zero, the nonpositive cap of the signed hull volume. -/
def sourceThetaSigned : Real := 0

theorem sourceQ_negative : sourceQSigned (I := I) selectedLowerPlaces parameters < 0 :=
  ArithmeticQPilotGlobalNormalization.normalizedLowerSignedLog_neg
    selectedLowerPlaces parameters selected_nonempty

theorem sourceTarget_le_theta :
    sourceTargetSigned I v R n ≤ sourceThetaSigned :=
  I.sourceSignedHullLogVolume_nonpos v R n

/-- Exact source comparison needed for q_le_target. -/
def SourceQHullComparison : Prop :=
  sourceQSigned (I := I) selectedLowerPlaces parameters ≤
    sourceTargetSigned I v R n

/-- Actual finite-model IPL/SHE/APT propositions used as contract evidence. -/
def contractIPL : Prop := finiteIPLProposition l 0
def contractSHE : Prop := finiteSHEProposition l 0
def contractAPT : Prop := finiteAPTProposition l 0

theorem contractIPL_proved : contractIPL (l := l) := finiteIPLProposition_proved l 0
theorem contractSHE_proved : contractSHE (l := l) := finiteSHEProposition_proved l 0
theorem contractAPT_proved : contractAPT (l := l) := finiteAPTProposition_proved l 0

/-- Actual StepXIContract with qSigned/target/theta actual and finite evidence;
q_le_target is exactly SourceQHullComparison. -/
noncomputable def sourceContract
    (hq : SourceQHullComparison (I := I) (v := v) (R := R) (n := n)
      selectedLowerPlaces parameters) : StepXIContract :=
  StepXIContract.ofAbsoluteDegreeNormalizedSignedLog
    selectedLowerPlaces parameters selected_nonempty
    (sourceTargetSigned I v R n) sourceThetaSigned
    hq (sourceTarget_le_theta I v R n)
    (contractIPL (l := l)) (contractSHE (l := l)) (contractAPT (l := l))
    (contractIPL_proved (l := l)) (contractSHE_proved (l := l))
    (contractAPT_proved (l := l))

theorem sourceContract_conclusion
    (hq : SourceQHullComparison (I := I) (v := v) (R := R) (n := n)
      selectedLowerPlaces parameters) :
    Cor312Conclusion (sourceContract I v R n selectedLowerPlaces parameters hq) := by
  exact cor312_of_constructed_stepXI _

theorem sourceContract_q_negative
    (hq : SourceQHullComparison (I := I) (v := v) (R := R) (n := n)
      selectedLowerPlaces parameters) :
    (sourceContract I v R n selectedLowerPlaces parameters hq).qSigned < 0 := by
  exact (sourceContract I v R n selectedLowerPlaces parameters hq).q_negative

theorem sourceContract_q_le_target
    (hq : SourceQHullComparison (I := I) (v := v) (R := R) (n := n)
      selectedLowerPlaces parameters) :
    (sourceContract I v R n selectedLowerPlaces parameters hq).qSigned ≤
      (sourceContract I v R n selectedLowerPlaces parameters hq).targetSigned := by
  exact (sourceContract I v R n selectedLowerPlaces parameters hq).q_le_target

theorem sourceContract_target_le_theta
    (hq : SourceQHullComparison (I := I) (v := v) (R := R) (n := n)
      selectedLowerPlaces parameters) :
    (sourceContract I v R n selectedLowerPlaces parameters hq).targetSigned ≤
      (sourceContract I v R n selectedLowerPlaces parameters hq).thetaSigned := by
  exact (sourceContract I v R n selectedLowerPlaces parameters hq).target_le_theta

end LeanFormal.IUT.XiFPaper.S620FinalContractActualAdapted

end
