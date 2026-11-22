/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-! # A509 Gap 1 object: height ↔ comparison-region data (object, not a proof) -/

noncomputable section

namespace LeanFormal.IUT.Objects.Gap1

open LeanFormal.IUT

universe u

/-- The Gap 1 object: the data entering the height-vs-region-log-volume comparison, over a
literal hull/log-volume interface `W` (the paper carrier).  It records the concrete
comparison region (`normalizedComparisonRegion ...`), the ABC triple, and the log-height of
its rational point.  It does **not** assert the comparison itself; Gap 1 is the statement
that `height <= (1+eps) * logVolume region` for this data. -/
structure Gap1Object (X : Type u) (W : IQHullLogVolumeInterface X) where
  /-- Numerator of the rational point. -/
  a : Nat
  /-- Lower term. -/
  b : Nat
  /-- Denominator. -/
  c : Nat
  /-- The triple is an ABC triple. -/
  triple : IsABCTriple a b c
  /-- The paper point of the carrier attached to the rational point. -/
  logShellPoint : Nat → Nat → Nat → X
  /-- The concrete comparison region of the point. -/
  region : Set X
  region_eq : region = normalizedComparisonRegion W logShellPoint a b c
  /-- The log-height of the rational point. -/
  height : ℝ
  height_eq : height = Height.logHeight₁ (abcRationalPoint a c)
  /-- The comparison parameter. -/
  eps : ℝ
  eps_pos : 0 < eps

/-- The Gap 1 object attached to concrete data (interface, point assignment, triple, ε). -/
def gap1ObjectOf (X : Type u) (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) (a b c : Nat) (h : IsABCTriple a b c)
    (eps : ℝ) (heps : 0 < eps) : Gap1Object X W where
  a := a
  b := b
  c := c
  triple := h
  logShellPoint := logShellPoint
  region := normalizedComparisonRegion W logShellPoint a b c
  region_eq := rfl
  height := Height.logHeight₁ (abcRationalPoint a c)
  height_eq := rfl
  eps := eps
  eps_pos := heps

/-- The region volume of a Gap 1 object: the interface log-volume of its comparison region. -/
def Gap1Object.regionVolume {X : Type u} {W : IQHullLogVolumeInterface X}
    (D : Gap1Object X W) : ENNReal :=
  W.logVolume D.region

/-- The Gap 1 comparison statement as a predicate on the object (the named content, not
proved here): the height is bounded by `(1+ε)` times the region's real log-volume. -/
def Gap1Object.Statement {X : Type u} {W : IQHullLogVolumeInterface X}
    (D : Gap1Object X W) : Prop :=
  D.height ≤ (1 + D.eps) * (W.logVolume D.region).toReal

end LeanFormal.IUT.Objects.Gap1
