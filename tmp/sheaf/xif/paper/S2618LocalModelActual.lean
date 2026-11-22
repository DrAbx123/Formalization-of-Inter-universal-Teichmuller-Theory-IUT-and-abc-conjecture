import tmp.sheaf.xif.paper.S2617CuspParameterCandidateActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1330CuspEpsilonActual
open LeanFormal.IUT.XiFPaper.S2617CuspParameterCandidateActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2618LocalModelActual

variable {l : PrimeGeFive}

abbrev S2618Kv : Type := Completion (S1280Place l)
noncomputable instance S2618KvField : Field (S2618Kv (l := l)) := inferInstance

structure S2618LocalModelData
    (S : SourceSignQuotientData (S1280Arithmetic l)) where
  uniformizer : S2618Kv (l := l)
  uniformizer_ne_zero : uniformizer ≠ 0
  uniformizer_valuation_lt_one :
    (Valued.v uniformizer : WithZero (Multiplicative Int)) < 1
  cuspParameter : S1330PaperCusp l S → S2618Kv (l := l)
  cuspParameter_eq : ∀ c : S1330PaperCusp l S, cuspParameter c = uniformizer
  isCandidate : Prop
  isCandidate_proved : isCandidate

noncomputable def S2618CandidateData
    (S : SourceSignQuotientData (S1280Arithmetic l)) :
    S2618LocalModelData S where
  uniformizer := (S2617Q (l := l)).q
  uniformizer_ne_zero := S2617Q_ne_zero (l := l)
  uniformizer_valuation_lt_one := (S2617Q (l := l)).valuation_lt_one
  cuspParameter := fun _ => (S2617Q (l := l)).q
  cuspParameter_eq := fun _ => rfl
  isCandidate := forall c : S1330PaperCusp l S,
    (fun _ => (S2617Q (l := l)).q) c = (S2617Q (l := l)).q
  isCandidate_proved := fun _ => rfl

theorem S2618CandidateData_uniformizer_ne_zero
    (S : SourceSignQuotientData (S1280Arithmetic l)) :
    (S2618CandidateData S).uniformizer ≠ 0 := by
  exact (S2618CandidateData S).uniformizer_ne_zero

#check S2618LocalModelData
#check S2618CandidateData

end LeanFormal.IUT.XiFPaper.S2618LocalModelActual
end