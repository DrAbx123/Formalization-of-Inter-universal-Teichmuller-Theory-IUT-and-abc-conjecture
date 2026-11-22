import tmp.sheaf.xif.paper.PaperQPilotObject
import tmp.sheaf.xif.paper.PaperQPilotLogVolume
import tmp.sheaf.xif.paper.ConcreteC3DonorActual
import tmp.sheaf.xif.paper.ConcreteQPilotLogIdentificationActual

/-! # Concrete source-q identification: actual formulas and exact obstruction

The actual source scalar is

  sourceQPilotSignedLog S =
    - sum_{b : S.badPlaces} |log (S.reduction.qParameter b)|.

The actual C3 local scalar is

  localSignedLog C3.q = Real.log ||C3.q.q||.

The requested equality

  ConcreteSourceQIdentification :=
    sourceQPilotSignedLog I.initial = localSignedLog C3.q

therefore unfolds to the exact equality

  - sum_b |log q_b| = Real.log ||C3.q.q||.

This file proves the unfolding/formula theorems and records the equality as the
exact missing source-q identification.  It does not fabricate a proof: the
concrete source data do not relate the real qParameter family to the completion
q candidate C3.q.  No inequality/True/toy/axiom/sorry. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.Theorem311Source.ConcreteSourceQIdentificationActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotLogVolume

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The actual source q-pilot signed scalar as the negative sum of the bad
q-parameter absolute logs. -/
theorem sourceQPilotSignedLog_eq_neg_sum_abs_log :
    sourceQPilotSignedLog I.initial = -sourceBadQAbsLog I.initial := by
  unfold sourceQPilotSignedLog
  rfl

/-- The actual C3 local signed q-log as the log norm of the completion q. -/
theorem localSignedLog_C3_eq_log_norm :
    localSignedLog C3.q = Real.log ‖C3.q.q‖ := rfl

/-- The requested source-q identification. -/
def ConcreteSourceQIdentification : Prop :=
  sourceQPilotSignedLog I.initial = localSignedLog C3.q

/-- Exact unfolded form of the source-q identification: the negative bad
q-parameter log sum equals the C3 completion log-norm. -/
def ConcreteSourceQIdentificationFormula : Prop :=
  -sourceBadQAbsLog I.initial = Real.log ‖C3.q.q‖

/-- The source-q identification is exactly its formula form. -/
theorem concreteSourceQIdentification_iff_formula :
    ConcreteSourceQIdentification (I := I) C3 ↔
      ConcreteSourceQIdentificationFormula (I := I) C3 := by
  unfold ConcreteSourceQIdentification ConcreteSourceQIdentificationFormula
  rw [sourceQPilotSignedLog_eq_neg_sum_abs_log,
    localSignedLog_C3_eq_log_norm]

/-- Exact obstruction: the missing equalities are exactly the formula equality;
the concrete source supplies no relation between qParameter and C3.q. -/
def ConcreteSourceQIdentificationObstruction : Prop :=
  ConcreteSourceQIdentificationFormula (I := I) C3

/-- The obstruction is exactly the requested equality, not a True placeholder. -/
theorem concreteSourceQIdentificationObstruction_iff :
    ConcreteSourceQIdentification (I := I) C3 ↔
      ConcreteSourceQIdentificationObstruction (I := I) C3 :=
  concreteSourceQIdentification_iff_formula C3

/-- Conditional actual proof: the requested source-q identification follows
from the exact formula equality. -/
theorem concreteSourceQIdentification_of_formula
    (h : ConcreteSourceQIdentificationFormula (I := I) C3) :
    ConcreteSourceQIdentification (I := I) C3 :=
  (concreteSourceQIdentification_iff_formula C3).mpr h

end LeanFormal.IUT.Theorem311Source.ConcreteSourceQIdentificationActual

end
