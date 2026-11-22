/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import Mathlib.Tactic

/-! ## A943 update: E1 failure affects E4 usage

`Mzk1E1ExplicitCounterexampleActual` proves the paper bare E1 equality is false
for explicit q candidates (see `bareE1_false_for_explicit_local_q`).  E4 must
therefore not be combined with a bare E1 normalization; use
`E1AllocationForm V_norm V_hull qSide` (`Mzk1E1OrderActual`) as the correct
allocation interface.  E4 itself remains an interface (not proved for actual P).
-/

/-! ## Audit status (A933)

Status: **MODEL / INTERFACE** (not a theorem) — **PARTIAL**.
Route/stage: paper chain, E4 dictionary (A930/A933).
Date/author: 2026-11-12; lane hull.
试金石：本文件不主张不等式；E4 是接口/条件，`3^k−1` 信息未进入，
显式 defer 至下游 A3/B1/C3 定理化时回答 Q1–Q4。

- E4 is NOT proved for the actual lana P/VolShell: `E4Dictionary` is an
  interface; no construction of P or VolShell is given here.
- actual `PaperQPilotObjectActual` construction = **GAP** (see A931).
- The only proved content is the definitional equivalence and the conditional
  consumers (`e4_inequality`, `e4_of_unconditional`).
-/

/-! # A930 hull: E4 dictionary interface

Paper dictionary E4: if the q-pilot region is contained in P, then
`(sF-1)*A <= VolShell P`.
This file gives the compilable interface and conditional consumers; it does NOT
prove E4 for the actual lana objects (no construction of P / VolShell here). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1E4DictionaryActual

/-- Region containment as a Prop. -/
def RegionLe {α : Type*} (R P : Set α) : Prop := R ⊆ P

/-- E4 dictionary shape: containment implies the volume inequality. -/
def E4Dictionary {α : Type*} (R P : Set α) (sF A VolShell : ℝ) : Prop :=
  RegionLe R P → (sF - 1) * A ≤ VolShell

theorem E4Dictionary_iff {α : Type*} (R P : Set α) (sF A VolShell : ℝ) :
    E4Dictionary R P sF A VolShell ↔
      (RegionLe R P → (sF - 1) * A ≤ VolShell) := Iff.rfl

/-- Conditional consumer: E4 + containment gives the inequality. -/
theorem e4_inequality {α : Type*} {R P : Set α} {sF A VolShell : ℝ}
    (hE4 : E4Dictionary R P sF A VolShell) (hsub : RegionLe R P) :
    (sF - 1) * A ≤ VolShell := hE4 hsub

/-- E4 holds automatically if the volume inequality is unconditional. -/
theorem e4_of_unconditional {α : Type*} {R P : Set α} {sF A VolShell : ℝ}
    (h : (sF - 1) * A ≤ VolShell) : E4Dictionary R P sF A VolShell := fun _ => h

structure E4Witness {α : Type*} (R P : Set α) (sF A VolShell : ℝ) where
  containment : RegionLe R P
  volume_ineq : (sF - 1) * A ≤ VolShell

theorem e4_of_witness {α : Type*} {R P : Set α} {sF A VolShell : ℝ}
    (w : E4Witness R P sF A VolShell) : E4Dictionary R P sF A VolShell :=
  fun _ => w.volume_ineq

def e4Rows : List (String × String × String) :=
  [ ("RegionLe", "R ⊆ P", "DEF"),
    ("E4Dictionary", "R ⊆ P -> (sF-1)A <= VolShell", "DEF"),
    ("E4Dictionary_iff", "definitional equivalence", "PROVED"),
    ("e4_inequality", "E4 + containment -> inequality", "PROVED"),
    ("e4_of_unconditional", "unconditional inequality -> E4", "PROVED"),
    ("E4Witness", "containment + volume inequality", "DEF") ]

theorem e4Rows_length : e4Rows.length = 6 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1E4DictionaryActual.E4Dictionary_iff
#print axioms LeanFormal.IUT.XiFPaper.Mzk1E4DictionaryActual.e4_inequality
#print axioms LeanFormal.IUT.XiFPaper.Mzk1E4DictionaryActual.e4_of_unconditional

end LeanFormal.IUT.XiFPaper.Mzk1E4DictionaryActual

end