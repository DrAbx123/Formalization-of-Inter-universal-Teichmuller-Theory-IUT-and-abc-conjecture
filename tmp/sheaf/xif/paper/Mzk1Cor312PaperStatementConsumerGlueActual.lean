import tmp.sheaf.xif.paper.Mzk1Cor312PaperStatementActual
import tmp.sheaf.xif.paper.Mzk1Cor312NumericalContentActual

/-! # Mzk1Cor312PaperStatementConsumerGlueActual — paper statement vs numerical 3.12 content

A541 consumer module (no new mathematics): connects the abstract paper statement of
Corollary 3.12 with the exact numerical instance of Unit X (mu_q = -1/2 L,
mu_theta = -1/6 L).  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312PaperStatementConsumerGlueActual

open LeanFormal.IUT.XiFPaper.Mzk1Cor312PaperStatementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312NumericalContentActual

/-- The numerical Unit X instance is a paper statement instance for L = 1. -/
theorem numerical_paperInstance (L : Real) (hL : 0 < L) :
    Cor312PaperStatement :=
  { thetaLog := muTheta L, qLog := muQ L,
    q_positive := by
      unfold muQ
      linarith
    q_le_theta := cor312_numerical_holds L hL,
    cTheta := -(1 / 6),
    calibrated := by
      unfold muTheta muQ
      ring }

/-- The constant conclusion at the numerical instance: `-1 <= -1/6`. -/
theorem numerical_cTheta_ge_neg_one (L : Real) (hL : 0 < L) :
    -1 <= (numerical_paperInstance L hL).cTheta :=
  Cor312PaperStatement.cTheta_ge_neg_one (numerical_paperInstance L hL)

/-- The numerical gap is a positive multiple of L (Unit X: (1/3)L). -/
theorem numerical_gap_paper (L : Real) (hL : 0 < L) :
    0 < (numerical_paperInstance L hL).thetaLog -
      (numerical_paperInstance L hL).qLog :=
  by
  have h := cor312_gap_pos L hL
  simpa [numerical_paperInstance, muTheta, muQ] using h

#check numerical_paperInstance
#check numerical_cTheta_ge_neg_one
#check numerical_gap_paper

end LeanFormal.IUT.XiFPaper.Mzk1Cor312PaperStatementConsumerGlueActual
end
