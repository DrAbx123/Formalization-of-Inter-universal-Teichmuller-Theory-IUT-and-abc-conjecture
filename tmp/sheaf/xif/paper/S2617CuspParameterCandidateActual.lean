import tmp.sheaf.xif.paper.S1428RealCuspValuationActual
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import tmp.sheaf.xif.paper.S1636SourceClausesActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1330CuspEpsilonActual
open LeanFormal.IUT.XiFPaper.S1428RealCuspValuationActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1636SourceClausesActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2617CuspParameterCandidateActual

variable {l : PrimeGeFive}

noncomputable def S2617Q :
    NumberFieldFinitePlace.FinitePlaceQCandidate (S1280Place l) :=
  Classical.choice (NumberFieldFinitePlace.finitePlaceQCandidate_nonempty (S1280Place l))

theorem S2617Q_ne_zero :
    (S2617Q (l := l)).q ≠ 0 :=
  (S2617Q (l := l)).q_ne_zero

variable (S : SourceSignQuotientData (S1280Arithmetic l))

noncomputable def S2617LocalParameterCandidate :
    S1428CuspLocalParameter l S where
  localParameter := fun _ => (S2617Q (l := l)).q
  localParameter_nonzero := fun _ => S2617Q_ne_zero (l := l)
  isActualCuspParameter := forall c : S1330PaperCusp l S,
    (fun _ => (S2617Q (l := l)).q) c = (S2617Q (l := l)).q
  isActualCuspParameter_proved := fun _ => rfl

theorem S2617CuspClause_nonempty
    (S : SourceSignQuotientData (S1280Arithmetic l)) :
    Nonempty SourceCuspClause :=
  let P := S2617LocalParameterCandidate S
  let c : S1330PaperCusp l S := S.epsilon
  ⟨S1636CuspClauseOfLocalParameter l S P c⟩

#check S2617LocalParameterCandidate
#check S2617CuspClause_nonempty

end LeanFormal.IUT.XiFPaper.S2617CuspParameterCandidateActual
end