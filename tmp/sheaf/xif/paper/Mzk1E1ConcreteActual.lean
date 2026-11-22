/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import tmp.sheaf.xif.paper.Mzk1E1DictionaryActual
import Mathlib.Tactic

/-! ## A943 update: bare E1 is FALSE on general data

`Mzk1E1ExplicitCounterexampleActual` (EXIT=0/olean/trio) proves, for the explicit
DVR q candidate at any actual finite place:
- `explicitQCandidate_qSide_ne_zero`,
- `bareE1_false_for_explicit_local_q : ¬ E1PaperScaledHullForm (QSideContribution ...)`.

Therefore the paper bare equality E1 is not the correct general interface.
The correct interface is `E1AllocationForm V_norm V_hull qSide` from
`Mzk1E1OrderActual`, with `e1_allocation_of_zero` reducing it to E1 exactly when
`qSide = 0`.  The order-zero theorem below remains valid as a conditional
sufficient condition, not as a general E1 proof.
-/

/-! ## Audit status (A933)

Status: **PROVED-CONDITIONAL + MODEL** — **PARTIAL** (not an unconditional theorem).
Route/stage: paper chain, E1 concrete verification (A930/A933).
Date/author: 2026-11-12; lane hull.
试金石：本文件不主张不等式；`3^k−1` 信息未进入，显式 defer 至下游
A3/B1/C3 定理化时回答 Q1–Q4。

- PROVED-CONDITIONAL: `order=0 => qSideContribution=0 => E1PaperScaledHull`, for an
  arbitrary given actual `P : PaperQPilotObjectActual`.
- MODEL: the l=5/{2}/{2,11} `ConcreteDatum` are model data, not actual P.
- GAP: actual `PaperQPilotObjectActual` construction and a proof that its q-order
  is 0 are NOT given here (A931: `QPilotIdentificationActual` not inhabited).
-/

/-! # A930 hull: E1 concrete verification (q-side zero)

Sufficient condition: if the q-pilot order `P.line.C3.q.order = 0`, then
`qSideContribution P = 0`, hence `E1PaperScaledHull` holds.
Concrete model data: l=5, bad set {2} or {2,11}, q order 0.
Label: the order-zero implication is PROVED for the green definitions; the
concrete l=5/{2}/{2,11} data is MODEL (no actual PaperQPilotObjectActual is
constructed here). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1E1ConcreteActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1VPaperActual
open LeanFormal.IUT.XiFPaper.Mzk1E1DictionaryActual
open scoped BigOperators ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- If the q-pilot order is 0, the q-side contribution vanishes. -/
theorem qSideContribution_eq_zero_of_order_zero
    (h : P.line.C3.q.order = 0) : qSideContribution P = 0 := by
  unfold qSideContribution
  rw [h]
  norm_num

/-- Consequently E1 holds for this P in every capsule. -/
theorem E1PaperScaledHull_of_order_zero (k : ℕ)
    (h : P.line.C3.q.order = 0) : E1PaperScaledHull T P k := by
  rw [E1PaperScaledHull_iff_qSide_zero]
  exact qSideContribution_eq_zero_of_order_zero P h

/-- Concrete model datum for l=5 with a prescribed bad set and q order 0. -/
structure ConcreteDatum where
  l : ℕ
  l_eq : l = 5
  bad : Finset ℕ
  qOrder : ℤ
  qOrder_zero : qOrder = 0
  base : ℝ
  base_pos : 0 < base

/-- Model q-side: order * log(base). -/
noncomputable def concreteQSide (D : ConcreteDatum) : ℝ :=
  (D.qOrder : ℝ) * Real.log D.base

theorem concreteQSide_eq_zero (D : ConcreteDatum) : concreteQSide D = 0 := by
  unfold concreteQSide
  rw [D.qOrder_zero]
  norm_num

/-- l=5, bad = {2}. -/
def datum_l5_two : ConcreteDatum where
  l := 5
  l_eq := rfl
  bad := {2}
  qOrder := 0
  qOrder_zero := rfl
  base := 2
  base_pos := by norm_num

/-- l=5, bad = {2,11}. -/
def datum_l5_two_eleven : ConcreteDatum where
  l := 5
  l_eq := rfl
  bad := {2, 11}
  qOrder := 0
  qOrder_zero := rfl
  base := 2
  base_pos := by norm_num

theorem qSide_l5_two_zero : concreteQSide datum_l5_two = 0 := concreteQSide_eq_zero _

theorem qSide_l5_two_eleven_zero : concreteQSide datum_l5_two_eleven = 0 := concreteQSide_eq_zero _

def e1Rows : List (String × String × String) :=
  [ ("qSideContribution", "order * log(residueNormBase)", "GREEN def"),
    ("order=0 => qSide=0", "generic actual P", "PROVED"),
    ("E1 order=0", "E1PaperScaledHull holds", "PROVED (E1PaperScaledHull_of_order_zero)"),
    ("l=5 bad {2}", "concrete model datum, qOrder=0 -> qSide=0", "MODEL + PROVED"),
    ("l=5 bad {2,11}", "concrete model datum, qOrder=0 -> qSide=0", "MODEL + PROVED"),
    ("actual P construction", "not constructed; concrete data are model-level", "GAP") ]

theorem e1Rows_length : e1Rows.length = 6 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1E1ConcreteActual.qSideContribution_eq_zero_of_order_zero
#print axioms LeanFormal.IUT.XiFPaper.Mzk1E1ConcreteActual.E1PaperScaledHull_of_order_zero
#print axioms LeanFormal.IUT.XiFPaper.Mzk1E1ConcreteActual.concreteQSide_eq_zero

end LeanFormal.IUT.XiFPaper.Mzk1E1ConcreteActual

end