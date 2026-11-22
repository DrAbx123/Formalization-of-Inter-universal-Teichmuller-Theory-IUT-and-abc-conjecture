/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegree
import tmp.sheaf.xif.paper.Mzk1P3UnramResidueActual
import Mathlib.Tactic

/-! # P3 bridge: ArithmeticQPilotBaseChange local indices = completion relative indices

Both pairs are defined by the same number-ring ramificationId/inertiaDegree expressions,
only in different namespaces; the bridges are rfl.  This turns RESDEG/UNRAM-RESIDUE
statements into the relative-index language of FinitePlaceCompletionDegree.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3ArithmeticRelativeBridgeActual

open LeanFormal.IUT.NumberFieldFinitePlace

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

theorem localResidueDegree_eq_relativeResidueDegree
    (place : NumberField.FinitePlace K) :
    LeanFormal.IUT.ArithmeticQPilotBaseChange.localResidueDegree (k := k) place =
      relativeResidueDegree (k := k) place := rfl

theorem localRamificationIndex_eq_relativeRamificationIndex
    (place : NumberField.FinitePlace K) :
    LeanFormal.IUT.ArithmeticQPilotBaseChange.localRamificationIndex (k := k) place =
      relativeRamificationIndex (k := k) place := rfl

theorem localResidueDegree_eq_one_iff_relativeResidueDegree_eq_one
    (place : NumberField.FinitePlace K) :
    LeanFormal.IUT.ArithmeticQPilotBaseChange.localResidueDegree (k := k) place = 1
      ↔ relativeResidueDegree (k := k) place = 1 := by
  rw [localResidueDegree_eq_relativeResidueDegree]

def bridgeRows : List (String × String × String) :=
  [ ("localResidueDegree_eq_relativeResidueDegree", "same number-ring inertiaDeg formula", "PROVED (rfl)"),
    ("localRamificationIndex_eq_relativeRamificationIndex", "same number-ring ramificationIdx formula", "PROVED (rfl)"),
    ("localResidueDegree_eq_one_iff_relativeResidueDegree_eq_one", "RESDEG in relative language", "PROVED") ]

theorem bridgeRows_length : bridgeRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P3ArithmeticRelativeBridgeActual

end
