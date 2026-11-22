import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1Section0PathCompositionV2Actual — pre-path/path composition (fresh path model)

Adapts the EXIT1 Section-0 path-composition file: an edge-sequence model of
pre-paths with length, nil, append and reverse laws.  No new math; no closure;
gate NOT PASSED; registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0PathCompositionV2Actual

structure PathData (V E : Type*) where
  start : V
  edges : List E
  finish : V

variable {V E : Type*}

def pdLength (p : PathData V E) : Nat := p.edges.length

def pdNil (v : V) : PathData V E := ⟨v, [], v⟩

def pdAppend (p q : PathData V E) (h : p.finish = q.start) : PathData V E :=
  ⟨p.start, p.edges ++ q.edges, q.finish⟩

def pdReverse (p : PathData V E) : PathData V E :=
  ⟨p.finish, p.edges.reverse, p.start⟩

def pdOfEdge (e : E) (u v : V) : PathData V E := ⟨u, [e], v⟩

@[simp] theorem pdNil_length (v : V) : pdLength (pdNil (E := E) v) = 0 := rfl

@[simp] theorem pdAppend_length (p q : PathData V E) (h : p.finish = q.start) :
    pdLength (pdAppend p q h) = pdLength p + pdLength q := by
  simp [pdLength, pdAppend]

theorem pdReverse_length (p : PathData V E) : pdLength (pdReverse p) = pdLength p := by
  simp [pdLength, pdReverse]

theorem pdReverse_reverse (p : PathData V E) : pdReverse (pdReverse p) = p := by
  cases p
  simp [pdReverse]

theorem pdOfEdge_length (e : E) (u v : V) : pdLength (pdOfEdge e u v) = 1 := rfl

def section0PathRows : List (String × String × String) :=
  [ ("path model", "PathData", "DEF (fresh)"),
    ("append length", "pdAppend_length", "PROVED"),
    ("reverse length", "pdReverse_length", "PROVED"),
    ("reverse involution", "pdReverse_reverse", "PROVED"),
    ("scope", "no new math; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem section0PathRows_length : section0PathRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Section0PathCompositionV2Actual

end
