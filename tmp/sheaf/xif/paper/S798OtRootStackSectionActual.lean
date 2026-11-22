import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
import tmp.sheaf.xif.paper.S795OrderSemanticsActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S798OtRootStackSectionActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S795OrderSemanticsActual
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

theorem stackQSection_divisor_order :
    stackDivisorSection T b (stackQSection T b) =
      Multiplicative.ofAdd ((qVFamily T b).order : Real) := rfl

theorem stackRootSection_divisor_order :
    stackDivisorSection T b (stackRootSection T b) =
      Multiplicative.ofAdd (((qVFamily T b).order : Real) / (2 * l.value)) := rfl

/-- The O-triangle(TX_v) root-stack section semantics carried by S782. -/
structure OtRootStackSectionData where
  sectionCarrier : Type
  monoid : Monoid sectionCarrier
  qSection : sectionCarrier
  rootSection : sectionCarrier
  root_pow : rootSection ^ (2 * l.value) = qSection
  divisorSection : sectionCarrier → Multiplicative Real
  q_divisor_eq : divisorSection qSection =
    Multiplicative.ofAdd ((qVFamily T b).order : Real)
  root_divisor_eq : divisorSection rootSection =
    Multiplicative.ofAdd (((qVFamily T b).order : Real) / (2 * l.value))

noncomputable def otRootStackSectionData : OtRootStackSectionData (l := l) T b where
  sectionCarrier := StackSectionCarrier T b
  monoid := inferInstance
  qSection := stackQSection T b
  rootSection := stackRootSection T b
  root_pow := stackRootSection_pow T b
  divisorSection := stackDivisorSection T b
  q_divisor_eq := stackQSection_divisor_order T b
  root_divisor_eq := stackRootSection_divisor_order T b

theorem otRootStackSection_carrier_eq :
    (otRootStackSectionData (l := l) T b).sectionCarrier = StackSectionCarrier T b := rfl

theorem otRootStackSection_q_divisor :
    (otRootStackSectionData (l := l) T b).divisorSection
        (otRootStackSectionData (l := l) T b).qSection =
      Multiplicative.ofAdd ((qVFamily T b).order : Real) :=
  stackQSection_divisor_order T b

theorem otRootStackSection_root_divisor :
    (otRootStackSectionData (l := l) T b).divisorSection
        (otRootStackSectionData (l := l) T b).rootSection =
      Multiplicative.ofAdd (((qVFamily T b).order : Real) / (2 * l.value)) :=
  stackRootSection_divisor_order T b

/-- The root-stack section is not an ordinary completion root. -/
theorem otRootStackSection_ordinary_root_absent :
    ¬ Nonempty (TwoLthRootData T b) :=
  ordinaryTwoLRootData_impossible (l := l) T b

/-- Paper q-pilot scalar from the root-stack section: the q[2u] divisor is
order/(2l), so the paper q-pilot log uses order/(2l) * log p. -/
noncomputable def otPaperQPilotLog : Real :=
  (stackDivisorSection T b (stackRootSection T b)).toAdd *
    Real.log (qVFamTensorP T b : Real)

theorem otPaperQPilotLog_eq :
    otPaperQPilotLog T b =
      (((qVFamily T b).order : Real) / (2 * l.value)) *
        Real.log (qVFamTensorP T b : Real) := by
  unfold otPaperQPilotLog
  rw [show stackDivisorSection T b (stackRootSection T b) =
      Multiplicative.ofAdd (((qVFamily T b).order : Real) / (2 * l.value)) from
    stackRootSection_divisor_order T b]
  rfl

/-- Paper theta hull log at the paper root coefficient order/(2l). -/
noncomputable def otPaperThetaHullLog
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] : Real :=
  rootThetaHullLog (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (paperRootCoefficientFamily T b)

/-- Paper target using the O-triangle root-stack q-pilot carrier. -/
def OtPaperTarget
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] : Prop :=
  otPaperQPilotLog T b ≤ otPaperThetaHullLog T b mu

end LeanFormal.IUT.XiFPaper.S798OtRootStackSectionActual
end