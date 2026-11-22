import tmp.sheaf.xif.paper.S2958HalfIQHullCertificateActual
import tmp.sheaf.xif.paper.S2715CThetaPaperScaleActual
import tmp.sheaf.xif.paper.S2691ExactQNormalizationActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2958HalfIQHullCertificateActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S2833S2800HregionActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
set_option maxHeartbeats 8000000
namespace LeanFormal.IUT.XiFPaper.S2959ParamProbe
example (theta : Real) :
    CThetaPaper S2958l 1 0
      (Real.exp ((theta + 1) /
          (((S2958l.value : Real) + 1) / 4 / paperQAbsLog S2958l 1) +
        (1 / 6) * (1 - 12 / ((S2958l.value : Real)) ^ 2))) 1 0 0 =
      theta := by
  unfold CThetaPaper cThetaBracket
  rw [Real.log_exp, Real.log_one]
  simp only [add_zero, mul_one, zero_mul, zero_add]
  have hne : paperQAbsLog S2958l 1 ≠ 0 := by
    unfold paperQAbsLog qNormFactor
    have hl : (0 : Real) < (S2958l.value : Real) := by
      unfold S2958l S2833l
      norm_num [fiveLabel]
    have h2 : (0 : Real) < 2 * (S2958l.value : Real) := by linarith
    exact mul_ne_zero (one_div_ne_zero (ne_of_gt h2)) one_ne_zero
  field_simp [hne, paperQAbsLog, qNormFactor]
  ring
end LeanFormal.IUT.XiFPaper.S2959ParamProbe
end