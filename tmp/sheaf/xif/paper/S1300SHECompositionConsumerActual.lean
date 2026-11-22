import tmp.sheaf.xif.paper.S1300HDDHullDetActual
import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual
import tmp.sheaf.xif.paper.GlobalThetaHullVsQPilotComparisonActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1300SHECompositionConsumerActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.GlobalThetaHullVsQPilotComparisonActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {l : PrimeGeFive} {V : Type uv} [Fintype V]
variable (I : Input Label Choice)
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (R : ∀ v : V, J.SourceImageRealization v) (n : ThetaPilotCarrier l)

theorem S1300SHECompositionConsumer_fields
    (D : S1300HDDHullDetSource I) :
    (D.toS1215 (I := I)).rank = D.rank ∧
    (∀ (m m' : Int) (j : SignedLabel l.value),
      Real.log (J.oneColumnScale m j) = Real.log (J.oneColumnScale m' j)) ∧
    (∀ (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I),
      (actualSHEOutput I).readingMap v o =
        (actualSHEOutput I).bundle.localization v unitSection) ∧
    (globalHullQPilotComparisonData (I := J) R n).hullLogVolume =
      globalThetaHullLogVolume (I := J) R n :=
  ⟨rfl, s1215LogShiftReadoutCompat_actual J, s1215IndeterminacySync_actual I, rfl⟩

#check S1300SHECompositionConsumer_fields
end LeanFormal.IUT.XiFPaper.S1300SHECompositionConsumerActual
end
