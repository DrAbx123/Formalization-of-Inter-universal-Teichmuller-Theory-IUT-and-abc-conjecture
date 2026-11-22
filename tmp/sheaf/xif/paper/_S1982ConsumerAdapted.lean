/-
Consumer re-check for S1982: the built olean must import and expose the
intended l = 5 signatures.
-/
import tmp.sheaf.xif.paper.S1982D5FiveActual

noncomputable section

open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1933PrePsiSeparableActual
open LeanFormal.IUT.Theorem311Source

#check @S1982Five
#check S1982Separability_five
#check S1982RankTwoBasisGap_five
#check S1982NatCard_LTorsion_five
#check S1982Finrank_five
#check S1982D5ExactFirstMissing
#check S1982D5ExactFirstMissing_iff_tail
#check S1982SourceTorsionClause_five

example : S1906Separability S1982Five := S1982Separability_five

example : S1725RankTwoBasisGap S1982Five := S1982RankTwoBasisGap_five

example : Nat.card (LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual.S1720Curve.LTorsion
    S1982Five) = 25 := S1982NatCard_LTorsion_five

example (h : S1982D5ExactFirstMissing) :
    SourceTorsionClause.{0, 0, 0} S1982Five :=
  S1982SourceTorsionClause_five h
