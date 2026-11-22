/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Section0PathCompositionActual

/-! # Reuse: projection/computation lemmas for path data -/

namespace LeanFormal.IUT.XiFPaper.Section0PathCompositionActual

variable {V E : Type*}

@[simp] theorem pdLength_eq_edges_length (p : PathData V E) :
    pdLength p = p.edges.length := rfl

@[simp] theorem pdAppend_start (p q : PathData V E) (h : p.end_ = q.start) :
    (pdAppend p q h).start = p.start := rfl

@[simp] theorem pdAppend_end (p q : PathData V E) (h : p.end_ = q.start) :
    (pdAppend p q h).end_ = q.end_ := rfl

@[simp] theorem pdAppend_edges (p q : PathData V E) (h : p.end_ = q.start) :
    (pdAppend p q h).edges = p.edges ++ q.edges := rfl

@[simp] theorem pdReverse_start (p : PathData V E) :
    (pdReverse p).start = p.end_ := rfl

@[simp] theorem pdReverse_end (p : PathData V E) :
    (pdReverse p).end_ = p.start := rfl

@[simp] theorem pdReverse_edges (p : PathData V E) :
    (pdReverse p).edges = p.edges.reverse := rfl

@[simp] theorem pdOfEdge_edges (e : E) (u v : V) :
    (pdOfEdge e u v).edges = [e] := rfl

@[simp] theorem pdOfEdge_start (e : E) (u v : V) :
    (pdOfEdge e u v).start = u := rfl

@[simp] theorem pdOfEdge_end (e : E) (u v : V) :
    (pdOfEdge e u v).end_ = v := rfl

end LeanFormal.IUT.XiFPaper.Section0PathCompositionActual
