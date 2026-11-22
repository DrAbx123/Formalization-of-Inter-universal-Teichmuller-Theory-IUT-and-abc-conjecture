import Mathlib

/-! # S813: weak-result interfaces for the paper hull/log comparison

The point of this file is interface-first: a weak or partial result is useful
once it exposes a typed interface.  Missing proofs become fields, not excuses.

No inhabitant is asserted for any interface field.  The final comparison is
conditional on the interface, so every remaining mathematical obligation is a
named field.
-/

namespace LeanFormal.IUT.XiFPaper.S813PaperInterfaceHub

/-- Minimal interface for the paper hull/log comparison. -/
structure PaperHullLogInterface (X : Type*) where
  hull : Set X
  qPilotRegion : Set X
  containment : qPilotRegion ⊆ hull
  qPilotLog : Real
  hullLog : Real
  log_le : qPilotLog ≤ hullLog

/-- Interface for a stacky/root-stack normalization of the hull log. -/
structure StackyHullLogInterface (X : Type*) extends PaperHullLogInterface X where
  stackyVolume : Real
  hullLog_eq_stacky : hullLog = stackyVolume

/-- Interface for a skeleton/tropical computation of the hull log. -/
structure SkeletonHullLogInterface (X : Type*) extends PaperHullLogInterface X where
  skeletonLength : Real
  hullLog_eq_skeleton : hullLog = skeletonLength

/-- Interface for a trace/index computation of the hull log. -/
structure TraceHullLogInterface (X : Type*) extends PaperHullLogInterface X where
  traceValue : Real
  hullLog_eq_trace : hullLog = traceValue

/-- Interface for a Gauss/moment identity producing the hull log. -/
structure GaussHullLogInterface (X : Type*) extends PaperHullLogInterface X where
  gaussValue : Real
  hullLog_eq_gauss : hullLog = gaussValue

/-- Interface for a p-adic/quaternionic Monge-Ampere computation. -/
structure PAdicMAHullLogInterface (X : Type*) extends PaperHullLogInterface X where
  maValue : Real
  hullLog_eq_ma : hullLog = maValue

/-- The target comparison, read off from any paper interface. -/
theorem PaperHullLogInterface.target {X : Type*} (I : PaperHullLogInterface X) :
    I.qPilotLog ≤ I.hullLog :=
  I.log_le

/-- A stacky interface gives the target through its stacky volume. -/
theorem StackyHullLogInterface.target {X : Type*} (I : StackyHullLogInterface X) :
    I.qPilotLog ≤ I.stackyVolume := by
  rw [← I.hullLog_eq_stacky]
  exact I.log_le

/-- A skeleton interface gives the target through skeleton length. -/
theorem SkeletonHullLogInterface.target {X : Type*} (I : SkeletonHullLogInterface X) :
    I.qPilotLog ≤ I.skeletonLength := by
  rw [← I.hullLog_eq_skeleton]
  exact I.log_le

/-- A trace interface gives the target through the trace value. -/
theorem TraceHullLogInterface.target {X : Type*} (I : TraceHullLogInterface X) :
    I.qPilotLog ≤ I.traceValue := by
  rw [← I.hullLog_eq_trace]
  exact I.log_le

/-- A Gauss interface gives the target through the Gauss value. -/
theorem GaussHullLogInterface.target {X : Type*} (I : GaussHullLogInterface X) :
    I.qPilotLog ≤ I.gaussValue := by
  rw [← I.hullLog_eq_gauss]
  exact I.log_le

/-- A p-adic MA interface gives the target through the MA value. -/
theorem PAdicMAHullLogInterface.target {X : Type*} (I : PAdicMAHullLogInterface X) :
    I.qPilotLog ≤ I.maValue := by
  rw [← I.hullLog_eq_ma]
  exact I.log_le

/-- Generic comparison tool: any distant-field invariant that computes the
paper hull and qPilot values can implement this interface. -/
structure PaperComparisonTool (X : Type*) where
  hull : Set X
  qPilotRegion : Set X
  containment : qPilotRegion ⊆ hull
  qPilotLog : Real
  hullLog : Real
  toolValue : Set X → Real
  toolValue_hull : toolValue hull = hullLog
  toolValue_qPilot : toolValue qPilotRegion = qPilotLog
  tool_comparison : toolValue qPilotRegion ≤ toolValue hull

/-- Any generic tool gives the paper target. -/
theorem PaperComparisonTool.target {X : Type*} (T : PaperComparisonTool X) :
    T.qPilotLog ≤ T.hullLog := by
  rw [← T.toolValue_qPilot, ← T.toolValue_hull]
  exact T.tool_comparison

/-- Convert a generic tool into the paper interface. -/
def PaperComparisonTool.toPaperHullLogInterface {X : Type*}
    (T : PaperComparisonTool X) : PaperHullLogInterface X where
  hull := T.hull
  qPilotRegion := T.qPilotRegion
  containment := T.containment
  qPilotLog := T.qPilotLog
  hullLog := T.hullLog
  log_le := T.target

end LeanFormal.IUT.XiFPaper.S813PaperInterfaceHub
