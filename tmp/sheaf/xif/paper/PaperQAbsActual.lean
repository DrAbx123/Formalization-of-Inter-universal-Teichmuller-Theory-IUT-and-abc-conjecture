/- Paper |log q| normalization. -/
import tmp.sheaf.xif.paper.S2959PaperParamsActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.PaperQAbsActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S2959PaperParamsActual
/-- Actual paper |log q| = logQ/(2l), for nonnegative logQ. -/
theorem paperQAbs_eq_abs_div (l : PrimeGeFive) {logQ : Real} (h : 0 ≤ logQ) :
    paperQAbsLog l logQ = |logQ| / (2 * (l.value : Real)) :=
  paperQAbsLog_eq_abs_div l h
/-- For a paper parameter source, qAbs is the actual paper normalized log. -/
theorem paperQAbs_of_source {a b c : Nat} (P : PaperParamSource a b c) :
    paperQAbsLog P.l P.logQ = |P.logQ| / (2 * (P.l.value : Real)) :=
  paperQAbs_eq_abs_div P.l (le_of_lt P.logQ_pos)
#check paperQAbs_eq_abs_div
#check paperQAbs_of_source
end LeanFormal.IUT.XiFPaper.PaperQAbsActual
end
