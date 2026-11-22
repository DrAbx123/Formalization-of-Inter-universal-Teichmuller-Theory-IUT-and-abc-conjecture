import tmp.sheaf.xif.paper.S2618CuspUniformizerNoGoActual
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

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
open LeanFormal.IUT.XiFPaper.S2618CuspUniformizerNoGoActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2619CuspUniformizerActual

variable {l : PrimeGeFive}
variable {S : SourceSignQuotientData (S1280Arithmetic l)}

/-- The actual completed-DVR uniformizer at the place above 5. -/
noncomputable def S2619Candidate :
    FinitePlaceQCandidate (S1280Place l) :=
  Classical.choice (finitePlaceQCandidate_nonempty (S1280Place l))

/-- The actual cusp local parameter obtained from the uniformizer; it is
constant across the paper cusps and hence uniformizer-valued everywhere. -/
noncomputable def S2619LocalParameter :
    S1428CuspLocalParameter l S where
  localParameter _ := S2619Candidate (l := l).q
  localParameter_nonzero _ := S2619Candidate (l := l).q_ne_zero
  isActualCuspParameter :=
    (Valued.v (S2619Candidate (l := l)).q : WithZero (Multiplicative Int)) < 1
  isActualCuspParameter_proved :=
    S2619Candidate (l := l).valuation_lt_one

theorem S2619LocalParameter_norm_lt_one :
    ∀ c : S1330PaperCusp l S,
      ‖(S2619LocalParameter (l := l) (S := S)).localParameter c‖ < 1 := by
  intro c
  change ‖(S2619Candidate (l := l)).q‖ < 1
  exact (Valued.toNormedField.norm_lt_one_iff).mpr
    (S2619Candidate (l := l)).valuation_lt_one

/-- Actual D8 uniformizer input. -/
noncomputable def S2619CuspUniformizer :
    S2618CuspUniformizer l S where
  toLocalParameter := S2619LocalParameter
  norm_lt_one := S2619LocalParameter_norm_lt_one

theorem S2619CuspUniformizerRequired :
    S2618CuspUniformizerRequired l S :=
  ⟨S2619CuspUniformizer⟩

/-- Actual D8 cusp clause from the constructed uniformizer. -/
noncomputable def S2619CuspClause
    (c : S1330PaperCusp l S) : SourceCuspClause :=
  S2618CuspClauseOfUniformizer (l := l) (S := S) S2619CuspUniformizer c

theorem S2619CuspClause_epsilon_lt_one
    (c : S1330PaperCusp l S) :
    (S2619CuspClause c).epsilon < 1 := by
  rw [S2619CuspClause]
  exact S2619LocalParameter_norm_lt_one c

#print axioms S2619CuspUniformizer
#print axioms S2619CuspClause_epsilon_lt_one

end LeanFormal.IUT.XiFPaper.S2619CuspUniformizerActual
end
