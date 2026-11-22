import tmp.sheaf.xif.paper.S2617CuspClauseReductionActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1330CuspEpsilonActual
open LeanFormal.IUT.XiFPaper.S1428RealCuspValuationActual
open LeanFormal.IUT.XiFPaper.S2616CuspAssemblyActual
open LeanFormal.IUT.XiFPaper.S2617CuspClauseReductionActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2618CuspUniformizerNoGoActual

variable {l : PrimeGeFive}
variable {S : SourceSignQuotientData (S1280Arithmetic l)}

noncomputable def S2618TrivialLocalParameter :
    S1428CuspLocalParameter l S where
  localParameter _ := (1 : Completion (S1280Place l))
  localParameter_nonzero _ := one_ne_zero
  isActualCuspParameter := ∀ c : S1330PaperCusp l S, (1 : Completion (S1280Place l)) ≠ 0
  isActualCuspParameter_proved := fun c => one_ne_zero

@[simp] theorem S2618TrivialLocalParameter_apply
    (c : S1330PaperCusp l S) :
    (S2618TrivialLocalParameter (l := l) (S := S)).localParameter c =
      (1 : Completion (S1280Place l)) := by
  simp [S2618TrivialLocalParameter]

theorem S2618TrivialLocalParameter_norm :
    ∀ c : S1330PaperCusp l S,
      ‖(S2618TrivialLocalParameter (l := l) (S := S)).localParameter c‖ =
        (1 : Real) := by
  intro c
  rw [S2618TrivialLocalParameter_apply]
  exact norm_one

theorem S2618TrivialLocalParameter_not_uniformizer :
    ¬ ∀ c : S1330PaperCusp l S,
      ‖(S2618TrivialLocalParameter (l := l) (S := S)).localParameter c‖ < 1 := by
  intro h
  have hc := h S.epsilon
  rw [S2618TrivialLocalParameter_apply] at hc
  rw [norm_one] at hc
  exact lt_irrefl (1 : Real) hc

structure S2618CuspUniformizer (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280Arithmetic l)) where
  toLocalParameter : S1428CuspLocalParameter l S
  norm_lt_one : ∀ c : S1330PaperCusp l S,
    ‖toLocalParameter.localParameter c‖ < 1

noncomputable def S2618CuspClauseOfUniformizer
    (U : S2618CuspUniformizer l S) (c : S1330PaperCusp l S) :
    SourceCuspClause :=
  S2616CuspClause (S := S) (P := U.toLocalParameter) c

def S2618CuspUniformizerRequired (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280Arithmetic l)) : Prop :=
  Nonempty (S2618CuspUniformizer l S)

theorem S2618CuspLocalParameter_not_enough
    (l : PrimeGeFive) (S : SourceSignQuotientData (S1280Arithmetic l)) :
    ¬ (∀ P : S1428CuspLocalParameter l S,
        ∀ c : S1330PaperCusp l S, ‖P.localParameter c‖ < 1) := by
  intro h
  exact S2618TrivialLocalParameter_not_uniformizer (l := l) (S := S)
    (fun c => h (S2618TrivialLocalParameter (l := l) (S := S)) c)

#print axioms S2618CuspClauseOfUniformizer
#print axioms S2618CuspLocalParameter_not_enough

end LeanFormal.IUT.XiFPaper.S2618CuspUniformizerNoGoActual
end
