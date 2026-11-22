/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Cor312StatementShapeActual
import Mathlib.Tactic.Linarith

/-! # A543: C_Theta >= -1 consumer (IUT III l.10351-10353) -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312CThetaConsumerActual

open LeanFormal.IUT.XiFPaper.Mzk1Cor312StatementShapeActual

/-- **Paper's `C_Theta >= -1`**: if `-|log Theta| >= -|log q|` and
`-|log Theta| <= C * |log q|` with `|log q| > 0`, then `C >= -1`. -/
theorem C_ge_neg_one_of_paper_statement (minusAbsLogTheta absLogQ C : ℝ)
    (hstmt : PaperCor312Statement minusAbsLogTheta (-absLogQ))
    (hC : PaperCThetaForm minusAbsLogTheta absLogQ C)
    (hq : 0 < absLogQ) :
    -1 ≤ C := by
  unfold PaperCor312Statement at hstmt
  unfold PaperCThetaForm at hC
  nlinarith

/-- The same conclusion from the signed form directly (convenience). -/
theorem C_ge_neg_one_of_signed (thetaSigned qSigned absLogQ C : ℝ)
    (h : qSigned ≤ thetaSigned) (hqSigned : qSigned = -absLogQ)
    (hC : thetaSigned ≤ C * absLogQ) (hq : 0 < absLogQ) :
    -1 ≤ C := by
  rw [hqSigned] at h
  nlinarith

end LeanFormal.IUT.XiFPaper.Mzk1Cor312CThetaConsumerActual
