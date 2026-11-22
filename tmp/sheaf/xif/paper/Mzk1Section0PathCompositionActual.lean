/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Section 0: pre-path/path composition (edge-sequence model) -/

namespace LeanFormal.IUT.XiFPaper.Section0PathCompositionActual

structure PathData (V E : Type*) where
  start : V
  edges : List E
  end_ : V

variable {V E : Type*}

def pdLength (p : PathData V E) : Nat := p.edges.length

def pdNil (v : V) : PathData V E :=
  ⟨v, [], v⟩

def pdAppend (p q : PathData V E) (h : p.end_ = q.start) : PathData V E :=
  ⟨p.start, p.edges ++ q.edges, q.end_⟩

def pdReverse (p : PathData V E) : PathData V E :=
  ⟨p.end_, p.edges.reverse, p.start⟩

def pdOfEdge (e : E) (u v : V) : PathData V E :=
  ⟨u, [e], v⟩

@[simp] theorem pdNil_length (v : V) : pdLength (pdNil (E := E) v) = 0 := rfl

@[simp] theorem pdAppend_length (p q : PathData V E) (h : p.end_ = q.start) :
    pdLength (pdAppend p q h) = pdLength p + pdLength q := by
  simp [pdLength, pdAppend]

theorem pdReverse_length (p : PathData V E) : pdLength (pdReverse p) = pdLength p := by
  simp [pdLength, pdReverse]

theorem pdReverse_reverse (p : PathData V E) : pdReverse (pdReverse p) = p := by
  cases p
  simp [pdReverse]

theorem pdReverse_nil (v : V) : pdReverse (pdNil (E := E) v) = pdNil (E := E) v := rfl

theorem pdOfEdge_length (e : E) (u v : V) : pdLength (pdOfEdge e u v) = 1 := rfl

end LeanFormal.IUT.XiFPaper.Section0PathCompositionActual