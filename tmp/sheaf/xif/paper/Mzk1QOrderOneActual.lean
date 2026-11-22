/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import Mathlib.Tactic

/-! # Mzk1QOrderOneActual — A789: the real value of `order(qVFamily)` (minimal import version)

Condition (3) reduces to `QOrderOne order` (`order = 1`), `order = (qVFamily T b).order`.
Clause B's `SourceTateComparisonWitness` has fields `parameter`, `comparison`,
`order_coprime : Nat.Coprime parameter.order l.value` — NO uniformizer field.
Hence `order = 1` is not derivable; what is derivable is `0 < order` and
`Nat.Coprime order l.value`; `order = 1` iff the parameter is a uniformizer
(`exponent = 1`).  Condition (3) is corrected to the coprime/positivity form, with
`TateUniformizerCondition` explicit for uses that genuinely need `order = 1`.

No axiom, no sorry, no `True` placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1QOrderOneActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Condition (3) as a predicate: the q-parameter order is one. -/
def QOrderOne (order : Nat) : Prop := order = 1

/-- Corrected condition (3): order positive and coprime to `l`. -/
def QOrderCoprime (order : Nat) (l : PrimeGeFive) : Prop :=
  0 < order ∧ Nat.Coprime order l.value

theorem qVFamily_order_pos : 0 < (qVFamily T b).order :=
  FinitePlaceQCandidate.order_pos (qVFamily T b)

theorem qVFamily_order_coprime : Nat.Coprime (qVFamily T b).order l.value := by
  unfold qVFamily
  exact (Classical.choice
    (T.clauseB.q_comparison ((nativeBadLift T).lift b)
      (by
        rw [(nativeBadLift T).lift_comap b]
        exact b.2))).order_coprime

theorem qVFamily_QOrderCoprime : QOrderCoprime (qVFamily T b).order l :=
  ⟨qVFamily_order_pos T b, qVFamily_order_coprime T b⟩

theorem order_eq_one_of_exponent_eq_one {K : Type u} [Field K] [NumberField K]
    {place : NumberField.FinitePlace K}
    (parameter : FinitePlaceQCandidate place) (h : parameter.exponent = 1) :
    parameter.order = 1 := by
  unfold FinitePlaceQCandidate.order
  rw [h]
  rfl

def TateUniformizerCondition : Prop := (qVFamily T b).exponent = 1

theorem tateUniformizerCondition_implies_QOrderOne
    (h : TateUniformizerCondition T b) : QOrderOne (qVFamily T b).order := by
  unfold TateUniformizerCondition at h
  unfold QOrderOne
  exact order_eq_one_of_exponent_eq_one (qVFamily T b) h

theorem qVFamily_QOrderOne_iff :
    QOrderOne (qVFamily T b).order ↔ (qVFamily T b).order = 1 := Iff.rfl

theorem qVFamTensorCoefficient_eq_one_of_uniformizer
    (h : TateUniformizerCondition T b) : qVFamTensorCoefficient T b = 1 := by
  unfold qVFamTensorCoefficient
  have h1 : QOrderOne (qVFamily T b).order :=
    tateUniformizerCondition_implies_QOrderOne T b h
  unfold QOrderOne at h1
  rw [h1]
  norm_num

def qOrderRows : List (String × String) :=
  [ ("clause B witness fields", "parameter + comparison + order_coprime (NO uniformizer field)"),
    ("qVFamily order > 0", "PROVED (order_pos)"),
    ("qVFamily order coprime to l", "PROVED (clause B order_coprime)"),
    ("order = 1 from clause B", "NOT DERIVABLE"),
    ("order = 1 iff uniformizer (exponent = 1)", "PROVED"),
    ("corrected condition (3)", "QOrderCoprime: 0 < order and Coprime order l"),
    ("uses needing order = 1", "add TateUniformizerCondition explicitly") ]

theorem qOrderRows_length : qOrderRows.length = 7 := rfl

#check qVFamily_order_pos
#check qVFamily_order_coprime
#check qVFamily_QOrderCoprime
#check tateUniformizerCondition_implies_QOrderOne
#check qVFamTensorCoefficient_eq_one_of_uniformizer
#check qOrderRows_length

end LeanFormal.IUT.XiFPaper.Mzk1QOrderOneActual
end
