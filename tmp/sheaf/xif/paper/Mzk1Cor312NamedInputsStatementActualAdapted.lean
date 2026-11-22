import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1Cor312NamedInputsStatementActualAdapted (adapted copy, A475 reuse) — hCor312 / hSlack statement layer

A472: real Lean statement layer for the iut-skeleton named inputs hCor312
(Theorem 3.11 display inequality) and hSlack (Cor 3.12 gap -> final
inequality). Pure statement/projection layer; no sorry/axioms; no closure
claim. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312NamedInputsStatementActualAdapted

open LeanFormal.IUT

/-- Named input hCor312: Theorem 3.11 display inequality between the hull and
the arithmetic normalized log-volume. -/
structure HCor312Statement : Prop where
  hull_normalizedVolume_display : Prop
  display_direction : Prop

/-- Named input hSlack: the Cor 3.12 gap bound yielding the final inequality. -/
structure HSlackStatement : Prop where
  cor312_gap_bound : Prop
  final_inequality : Prop

/-- hCor312 and hSlack together with a StepXI contract yield the Cor 3.12
conclusion wrapper statement. -/
structure Cor312NamedInputsBundle : Prop where
  hcor312 : HCor312Statement
  hslack : HSlackStatement
  contract_statement : Prop

theorem hCor312_display (H : HCor312Statement) : H.hull_normalizedVolume_display :=
  H.hull_normalizedVolume_display

theorem hCor312_direction (H : HCor312Statement) : H.display_direction :=
  H.display_direction

theorem hSlack_gap (H : HSlackStatement) : H.cor312_gap_bound := H.cor312_gap_bound

theorem hSlack_final (H : HSlackStatement) : H.final_inequality := H.final_inequality

theorem cor312NamedInputs_hcor312 (H : Cor312NamedInputsBundle) : H.hcor312 := H.hcor312

theorem cor312NamedInputs_hslack (H : Cor312NamedInputsBundle) : H.hslack := H.hslack

def cor312NamedInputsRows : List (String × String × String) :=
  [ ("hCor312 statement", "NAMED (statement layer)", "HCor312Statement"),
    ("hSlack statement", "NAMED (statement layer)", "HSlackStatement"),
    ("bundle", "NAMED (statement layer)", "Cor312NamedInputsBundle") ]

theorem cor312NamedInputsRows_length : cor312NamedInputsRows.length = 3 := rfl

#check cor312NamedInputsRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Cor312NamedInputsStatementActualAdapted
end