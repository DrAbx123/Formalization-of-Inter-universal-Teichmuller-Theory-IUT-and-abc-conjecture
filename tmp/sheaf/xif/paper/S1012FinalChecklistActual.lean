import tmp.sheaf.xif.paper.S1011GlobalWeightedFromS1004Actual
import tmp.sheaf.xif.paper.S1009HQHC3Actual
import tmp.sheaf.xif.paper.S1007QPilotPositivityActual
import tmp.sheaf.xif.paper.S1008S1004HullFiniteActual
import tmp.sheaf.xif.paper.S1023FractionalLatticeOpenActual

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S1012FinalChecklistActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1004QVFamFiniteLinearizationActual
open LeanFormal.IUT.XiFPaper.S1011GlobalWeightedFromS1004Actual
open LeanFormal.IUT.XiFPaper.S1009HQHC3Actual
open LeanFormal.IUT.XiFPaper.S1007QPilotPositivityActual
open LeanFormal.IUT.XiFPaper.S923RInteriorNonemptyActual
open LeanFormal.IUT.XiFPaper.S1023FractionalLatticeOpenActual
open LeanFormal.IUT.XiFPaper.S1008S1004HullFiniteActual
open MeasureTheory

universe u ua uv upi umon ui uL uC uG uX uLabel
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Updated exact checklist: positivity condition is F(cRoot) open (S1007);
finiteness is actual (S1008). -/
structure S1012FinalExactChecklist where
  fOpen : ∀ b : Bad (nativePlaceSelection T),
    S923FractionalLatticeOpen (l := l) T b
  sourceQ : Prop
  sourceLink : Prop
  finiteLinkEvidence : Prop

/-- Per-b positivity actual from S1023 openness. -/
theorem s1012Positivity (b : Bad (nativePlaceSelection T)) :
    0 < (s1004H (l := l) T b).measure (s1004QPilotImage (l := l) T b) :=
  s1007QPilotImage_measure_pos_of_open (l := l) T b
    (s923FractionalLatticeOpen_actual (l := l) T b)

/-- Per-b finiteness actual from S1008. -/
theorem s1012Finiteness (b : Bad (nativePlaceSelection T)) :
    (s1004H (l := l) T b).measure (s1004Hull (l := l) T b) < ⊤ :=
  s1008Hull_measure_lt_top (l := l) T b

/-- Actual global weighted inequality from S1007 positivity + S1008 finiteness. -/
theorem s1012GlobalWeighted_of_checklist :
    S919GlobalWeightedInequalityActual.weightedPaperV (l := l) T
        (S1011GlobalWeightedFromS1004Actual.s1011VR (l := l) T) ≤
      S919GlobalWeightedInequalityActual.weightedPaperV (l := l) T
        (S1011GlobalWeightedFromS1004Actual.s1011VS (l := l) T) :=
  S1011GlobalWeightedFromS1004Actual.s1011GlobalWeighted (l := l) T
    (fun b => s1012Positivity (l := l) T b)
    (fun b => s1012Finiteness (l := l) T b)


end LeanFormal.IUT.XiFPaper.S1012FinalChecklistActual
end
