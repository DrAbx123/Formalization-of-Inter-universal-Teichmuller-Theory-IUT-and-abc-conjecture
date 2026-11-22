/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic
/-! # AUDIT: HullDetObjectActual obsolete red gap rows -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HullDetObjectGapRowsActual
structure HullDetGapRow where
  item : String
  status : String
def hullDetGapRows : List HullDetGapRow :=
  [ ⟨"transitive O2ThetaObjectActual.olean", "missing; old API chain"⟩,
    ⟨"qPilotLogVolume C3 P signature", "API drift; current takes P only"⟩,
    ⟨"literalIQHullLogVolume C3 n", "API drift; C3 is implicit section var"⟩,
    ⟨"forall i, Fintype (tensorPlaceIndex i)", "not a field of SourcePilotRegionData"⟩,
    ⟨"Integers coercion rewrite", "old notation"⟩,
    ⟨"OB33 path", "replaced by Mzk1Ob33SourceIdentificationActual; no Lean consumer"⟩,
    ⟨"recommendation", "remove from watchdog list, mark DEFERRED, keep source; rewrite only if O6 needed"⟩ ]
theorem hullDetGapRows_length : hullDetGapRows.length = 7 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1HullDetObjectGapRowsActual
end