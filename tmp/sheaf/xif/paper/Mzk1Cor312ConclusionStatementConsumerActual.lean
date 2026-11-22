/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import tmp.sheaf.xif.paper.Mzk1Cor312StatementShapeActual
import Mathlib.Tactic.Linarith

/-! # A541: consumer — Cor312Conclusion implies the paper statement shape -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312ConclusionStatementConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Cor312StatementShapeActual

/-- A constructed StepXI contract yields the paper's `-|log Theta| >= -|log q|` shape,
with signed slots the negated magnitudes (paper reading convention). -/
theorem cor312Conclusion_to_paper_statement (C : StepXIContract) :
    PaperCor312Statement C.thetaSigned C.qSigned :=
  cor312_of_constructed_stepXI C

/-- Same consumer, stated with the magnitudes: from the contract's signed inequality
`qSigned <= thetaSigned`, the paper form `-|log q| >= ...` holds with
`minusAbsLogTheta := thetaSigned`, `minusAbsLogQ := qSigned`. -/
theorem cor312Conclusion_magnitudes (C : StepXIContract)
    (hqneg : C.qSigned < 0) :
    PaperCor312Statement C.thetaSigned C.qSigned ∧ C.qSigned < 0 :=
  ⟨cor312_of_constructed_stepXI C, hqneg⟩

end LeanFormal.IUT.XiFPaper.Mzk1Cor312ConclusionStatementConsumerActual
