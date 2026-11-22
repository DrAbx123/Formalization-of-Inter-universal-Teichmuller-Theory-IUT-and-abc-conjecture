import tmp.sheaf.xif.paper.S1095PushforwardHullEqActual
import tmp.sheaf.xif.paper.S1084IntegerWitnessActual
import tmp.sheaf.xif.paper.S1081LambdaODomainHaarActual

-- S1102: rootStackPaperThetaHull positivity/finiteness under
-- s1080PushforwardHaar, actual from S1095 pushforward identity +
-- S1084 domain positivity + S1081 domain finiteness.
-- The only exact input is S1095 measurability (embedding + region).

noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1102PushforwardHullPositivityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1073RootStackPaperThetaHullActual
open LeanFormal.IUT.XiFPaper.S1080PushforwardConstructionActual
open LeanFormal.IUT.XiFPaper.S1081LambdaODomainHaarActual
open LeanFormal.IUT.XiFPaper.S1084IntegerWitnessActual
open LeanFormal.IUT.XiFPaper.S1085PushforwardHullEqActual
open LeanFormal.IUT.XiFPaper.S1095PushforwardHullEqActual
open MeasureTheory Topology

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Exact input: measurability of embedding and hull region (S1095). -/
def S1102MeasurabilityInput : Prop :=
  S1095ExactMinimum (l := l) T b

theorem s1102PushforwardHullEq
    (h : S1102MeasurabilityInput (l := l) T b) :
    S1080PushforwardHullEq (l := l) T b :=
  s1095PushforwardHullEq_of_exact (l := l) T b h

/-- Actual hull positivity under s1080PushforwardHaar. -/
theorem s1102Hull_positivity_actual
    (h : S1102MeasurabilityInput (l := l) T b) :
    0 < s1080PushforwardHaar (l := l) T b
      (rootStackPaperThetaHull (l := l) T b) :=
  s1080Hull_positivity_of_domain (l := l) T b
    (s1102PushforwardHullEq (l := l) T b h)
    (s1084DomainPositivity_actual (l := l) T b)

/-- Actual hull finiteness under s1080PushforwardHaar. -/
theorem s1102Hull_finiteness_actual
    (h : S1102MeasurabilityInput (l := l) T b) :
    s1080PushforwardHaar (l := l) T b
      (rootStackPaperThetaHull (l := l) T b) < ⊤ :=
  s1080Hull_finiteness_of_domain (l := l) T b
    (s1102PushforwardHullEq (l := l) T b h)
    (s1081DomainFiniteness_actual (l := l) T b)

/-- Combined positivity and finiteness. -/
theorem s1102Hull_pos_fin_actual
    (h : S1102MeasurabilityInput (l := l) T b) :
    0 < s1080PushforwardHaar (l := l) T b
        (rootStackPaperThetaHull (l := l) T b) ∧
      s1080PushforwardHaar (l := l) T b
        (rootStackPaperThetaHull (l := l) T b) < ⊤ :=
  ⟨s1102Hull_positivity_actual (l := l) T b h,
    s1102Hull_finiteness_actual (l := l) T b h⟩

def S1102HullPosFinRequired : Prop :=
  S1102MeasurabilityInput (l := l) T b

#check s1102Hull_positivity_actual
#check s1102Hull_finiteness_actual
#check s1102Hull_pos_fin_actual

end LeanFormal.IUT.XiFPaper.S1102PushforwardHullPositivityActual

end