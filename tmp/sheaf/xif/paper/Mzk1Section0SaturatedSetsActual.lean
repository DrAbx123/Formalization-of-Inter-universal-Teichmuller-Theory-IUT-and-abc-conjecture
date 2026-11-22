/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Section 0: saturated sets of path pairs (edge-sequence model) -/

namespace LeanFormal.IUT.XiFPaper.Section0SaturatedSetsActual

variable {V E : Type*}

structure EdgePath (V E : Type*) where
  start : V
  edges : List E
  end_ : V

def epLength (p : EdgePath V E) : Nat := p.edges.length

def epMap (sigma : V → V) (p : EdgePath V E) : EdgePath V E :=
  ⟨sigma p.start, p.edges, sigma p.end_⟩

@[simp] theorem epLength_map (sigma : V → V) (p : EdgePath V E) :
    epLength (epMap sigma p) = epLength p := rfl

abbrev PathPair (V E : Type*) := EdgePath V E × EdgePath V E

def pairLength (p : PathPair V E) : Nat := epLength p.1 + epLength p.2

def pairMap (sigma : V → V) (p : PathPair V E) : PathPair V E :=
  (epMap sigma p.1, epMap sigma p.2)

@[simp] theorem pairLength_map (sigma : V → V) (p : PathPair V E) :
    pairLength (pairMap sigma p) = pairLength p := rfl

def EdgePreserving (G : V → V → Prop) (sigma : V → V) : Prop :=
  ∀ X Y : V, G X Y → G (sigma X) (sigma Y)

/-- A set of path pairs is saturated when membership is invariant under every
edge-preserving vertex map (the paper's saturated sets of path pairs, Section 0). -/
def Saturated (G : V → V → Prop) (P : Set (PathPair V E)) : Prop :=
  ∀ sigma : V → V, EdgePreserving G sigma → ∀ p : PathPair V E, p ∈ P ↔ pairMap sigma p ∈ P

theorem saturated_univ (G : V → V → Prop) :
    Saturated G (Set.univ : Set (PathPair V E)) := by
  intro sigma h p
  simp

theorem saturated_empty (G : V → V → Prop) :
    Saturated G (Set.empty : Set (PathPair V E)) := by
  intro sigma h p
  simp

theorem saturated_inter (G : V → V → Prop) {P Q : Set (PathPair V E)}
    (hP : Saturated G P) (hQ : Saturated G Q) :
    Saturated G (P ∩ Q) := by
  intro sigma h p
  rw [Set.mem_inter_iff, Set.mem_inter_iff, hP sigma h p, hQ sigma h p]

theorem saturated_iInter {ι : Type*} (G : V → V → Prop)
    (P : ι → Set (PathPair V E)) (h : ∀ i, Saturated G (P i)) :
    Saturated G (⋂ i, P i) := by
  intro sigma hsigma p
  simp only [Set.mem_iInter]
  exact forall_congr' (fun i => h i sigma hsigma p)

theorem saturated_mapsTo (G : V → V → Prop) {P : Set (PathPair V E)}
    (hP : Saturated G P) {sigma : V → V} (hsigma : EdgePreserving G sigma) :
    Set.MapsTo (pairMap sigma) P P :=
  fun p hp => (hP sigma hsigma p).mp hp

end LeanFormal.IUT.XiFPaper.Section0SaturatedSetsActual
