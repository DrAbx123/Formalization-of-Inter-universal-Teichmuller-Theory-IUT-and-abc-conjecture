import Mathlib

/-! # S889: scaling groupoid for pilot compatibility

User idea: encode compatibility of two pilots as a path in a higher
compatibility object, with log-volume as a local system.  This file gives the
generic bookkeeping: a directed graph (a one-dimensional skeleton of a
groupoid) whose edges carry a real scaling factor, a path scale, and a
log-volume function satisfying the edge law.  Reachability then gives the
comparison up to the accumulated path scale.

No paper identification is asserted here; instantiations with the actual
root/q/hull sections are separate files.
-/

namespace LeanFormal.IUT.XiFPaper.S889CompatibilityScalingGroupoid

/-- A graph whose edges carry a real scaling factor and whose vertices carry a
log-volume, with the local-system law on every edge. -/
structure ScalingGraph where
  Obj : Type
  Edge : Obj → Obj → Type
  step : {a b : Obj} → Edge a b → Real
  logVolume : Obj → Real
  edge_law : ∀ {a b : Obj} (e : Edge a b),
    logVolume b = step e * logVolume a

namespace ScalingGraph

variable (G : ScalingGraph)

/-- A path in the graph. -/
inductive Path : G.Obj → G.Obj → Type
  | nil (a : G.Obj) : Path a a
  | cons {a b c : G.Obj} (e : G.Edge a b) (p : Path b c) : Path a c

/-- Product of the edge scales along a path. -/
def Path.scale : {a b : G.Obj} → G.Path a b → Real
  | _, _, .nil _ => 1
  | _, _, .cons e p => G.step e * Path.scale p

/-- The local-system law along a path. -/
theorem Path.logVolume_eq : {a b : G.Obj} → (p : G.Path a b) →
    G.logVolume b = p.scale * G.logVolume a
  | _, _, .nil _ => by simp [Path.scale]
  | _, _, .cons e p => by
      simp only [Path.scale]
      rw [Path.logVolume_eq p, G.edge_law e]
      ring

/-- If every edge has scale one, log-volume is constant on a path. -/
theorem Path.logVolume_eq_of_scale_one
    (h : ∀ {a b : G.Obj} (e : G.Edge a b), G.step e = 1)
    {a b : G.Obj} (p : G.Path a b) :
    G.logVolume a = G.logVolume b := by
  have hscale : p.scale = 1 := by
    induction p with
    | nil => simp [Path.scale]
    | cons e p ih =>
        simp [Path.scale, h e, ih]
  rw [Path.logVolume_eq G p, hscale, one_mul]

/-- Reachability, as a proposition. -/
def Reachable (a b : G.Obj) : Prop := Nonempty (G.Path a b)

/-- Reachable vertices with scale-one path have equal log-volume. -/
theorem logVolume_eq_of_reachable_of_scale_one
    (h : ∀ {a b : G.Obj} (e : G.Edge a b), G.step e = 1)
    {a b : G.Obj} (hr : G.Reachable a b) :
    G.logVolume a = G.logVolume b := by
  obtain ⟨p⟩ := hr
  exact ScalingGraph.Path.logVolume_eq_of_scale_one G h p

end ScalingGraph

end LeanFormal.IUT.XiFPaper.S889CompatibilityScalingGroupoid
