import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false

/-!
# Countermodel for the ThreeAssumptions package without qPilotOutput_mem

This file is self-contained and does not edit C9Cor312ThreeAssumptions.lean.
It mirrors the abstract A1/A2/A3 fields except the membership field
qPilotOutput_mem, gives an instance satisfying all remaining fields where
the C1 inequality is false, and proves the membership field is load-bearing.
-/

namespace LeanFormal.IUT.N8Closure.C9ThreeAssumptionsCountermodel

/-- A1 abstract form, without the q-pilot output membership field. -/
structure Theorem311NoMem where
  Output : Type
  possibleOutputs : Set Output
  logVol : Output → ℝ
  qPilotOutput : Output

/-- A2 abstract form. -/
structure Prop39NoMem (T : Theorem311NoMem) where
  qLog : ℝ
  qLog_eq : qLog = T.logVol T.qPilotOutput

/-- A3 abstract form. -/
structure Remark395NoMem (T : Theorem311NoMem) where
  R : Set ℝ
  R_eq : R = T.logVol '' T.possibleOutputs
  h : ℝ
  hull_upper : ∀ x, x ∈ R → x ≤ h

/-- A1+A2+A3 without qPilotOutput_mem. -/
structure ThreeAssumptionsNoMem where
  T311 : Theorem311NoMem
  P39 : Prop39NoMem T311
  R395 : Remark395NoMem T311

/-- Countermodel data: one output type, no possible outputs, q-pilot value 1,
hull bound 0. -/
def counterT : Theorem311NoMem where
  Output := Unit
  possibleOutputs := ∅
  logVol := fun _ => 1
  qPilotOutput := ()

/-- The q-pilot output is not possible in the countermodel. -/
theorem counterT_qPilot_not_mem :
    counterT.qPilotOutput ∉ counterT.possibleOutputs := by
  change (() : Unit) ∉ (∅ : Set Unit)
  simp

/-- A2 holds in the countermodel, with qLog = 1. -/
def counterP : Prop39NoMem counterT where
  qLog := 1
  qLog_eq := rfl

/-- A3 holds in the countermodel: R = image of empty set = empty, h = 0. -/
def counterR : Remark395NoMem counterT where
  R := ∅
  R_eq := by
    simp [counterT]
  h := 0
  hull_upper := by
    intro x hx
    simp at hx

/-- All A1/A2/A3 structures except qPilotOutput_mem are satisfied. -/
def counterA : ThreeAssumptionsNoMem where
  T311 := counterT
  P39 := counterP
  R395 := counterR

/-- C1 fails in the countermodel: 1 ≤ 0 is false. -/
theorem counterA_C1_false : ¬ counterA.P39.qLog ≤ counterA.R395.h := by
  change ¬ (1 : ℝ) ≤ 0
  norm_num

/-- If the membership field were available in the countermodel, it would be
impossible, so the countermodel cannot be extended by that field. -/
theorem counterT_mem_impossible :
    ¬ (counterT.qPilotOutput ∈ counterT.possibleOutputs) :=
  counterT_qPilot_not_mem

/-- The membership field is load-bearing: with the same A1/A2/A3 data but the
membership hypothesis added, the standard C1 argument applies. -/
theorem C1_of_mem {T : Theorem311NoMem}
    (P : Prop39NoMem T) (R : Remark395NoMem T)
    (hmem : T.qPilotOutput ∈ T.possibleOutputs) :
    P.qLog ≤ R.h := by
  have hq : P.qLog ∈ R.R := by
    rw [R.R_eq, P.qLog_eq]
    exact ⟨T.qPilotOutput, hmem, rfl⟩
  exact R.hull_upper P.qLog hq

/-- Therefore the abstract ThreeAssumptions package without
qPilotOutput_mem is insufficient for C1: it has a model (counterA) in which
C1 is false, while adding membership makes C1 provable. -/
theorem qPilotOutput_mem_is_load_bearing :
    (¬ counterA.P39.qLog ≤ counterA.R395.h) ∧
    (∀ (T : Theorem311NoMem) (P : Prop39NoMem T) (R : Remark395NoMem T),
      T.qPilotOutput ∈ T.possibleOutputs → P.qLog ≤ R.h) :=
  ⟨counterA_C1_false, by
    intro T P R hmem
    exact C1_of_mem P R hmem⟩

end LeanFormal.IUT.N8Closure.C9ThreeAssumptionsCountermodel

end
