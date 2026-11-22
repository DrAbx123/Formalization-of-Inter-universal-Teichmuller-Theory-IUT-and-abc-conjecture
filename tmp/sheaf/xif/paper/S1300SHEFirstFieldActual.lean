import tmp.sheaf.xif.paper.S1300HDDHullDetActual
import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1300SHEFirstFieldActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {l : PrimeGeFive} {V : Type uv}
variable (I : Input Label Choice)
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

theorem S1300SHEFirstField_logShift_indeterminacy
    (D : S1300HDDHullDetSource I) :
    (D.toS1215 (I := I)).rank = D.rank ∧
    (∀ (m m' : Int) (j : SignedLabel l.value),
      Real.log (J.oneColumnScale m j) = Real.log (J.oneColumnScale m' j)) ∧
    (∀ (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I),
      (actualSHEOutput I).readingMap v o =
        (actualSHEOutput I).bundle.localization v unitSection) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro m m' j
    exact s1215LogShiftReadoutCompat_actual J m m' j
  · intro v o
    exact s1215IndeterminacySync_actual I v o

#check S1300SHEFirstField_logShift_indeterminacy
end LeanFormal.IUT.XiFPaper.S1300SHEFirstFieldActual
end
