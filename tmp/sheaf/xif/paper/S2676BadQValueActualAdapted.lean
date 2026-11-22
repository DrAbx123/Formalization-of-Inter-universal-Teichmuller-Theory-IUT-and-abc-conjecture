import tmp.sheaf.xif.paper.S1527OOrderEqualityActual
import tmp.sheaf.xif.paper.S1895OIdentificationsActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.OrigXiF

namespace LeanFormal.IUT.XiFPaper.S2676BadQValueActualAdapted

theorem S2676_qParameter_value (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    (S1280ReductionClause l).qParameter b =
      ((5 : ℝ)⁻¹) ^ S1527OrderC3 :=
  S1527_qParameter_eq l b

theorem S2676_abs_log_qParameter_value (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    |Real.log ((S1280ReductionClause l).qParameter b)| =
      (S1527OrderC3 : ℝ) * Real.log 5 :=
  S1527_abs_log_qParameter l b

theorem S2676_sourceBadQAbsLog_value (D : S1895PaperInput) :
    sourceBadQAbsLog (S1895PaperInput.I D).initial =
      (S1527OrderC3 : ℝ) * Real.log 5 := by
  rw [show (S1895PaperInput.I D).initial =
      S1527SourceData D.l D.R D.redCompat D.hredCompat D.torCompat
        D.htorCompat D.orbCompat D.horbCompat D.secCompat D.hsecCompat
        D.cusCompat D.hcusCompat from rfl]
  exact S1527_sourceBadQAbsLog D.l D.R D.redCompat D.hredCompat D.torCompat
    D.htorCompat D.orbCompat D.horbCompat D.secCompat D.hsecCompat
    D.cusCompat D.hcusCompat

theorem S2676_order_pos (l : PrimeGeFive) : 0 < S1527OrderC3 :=
  LeanFormal.IUT.Foundations.NumberField.FinitePlaceQCandidate.order_pos S1487Cand

theorem S2676_abs_log_ge_log5 (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    Real.log 5 ≤ |Real.log ((S1280ReductionClause l).qParameter b)| := by
  rw [S2676_abs_log_qParameter_value]
  have hpos : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have horder : (1 : ℝ) ≤ (S1527OrderC3 : ℝ) := by
    exact_mod_cast S2676_order_pos l
  nlinarith

#check S2676_qParameter_value
#check S2676_abs_log_qParameter_value
#check S2676_sourceBadQAbsLog_value
#check S2676_abs_log_ge_log5
#print axioms S2676_sourceBadQAbsLog_value

end LeanFormal.IUT.XiFPaper.S2676BadQValueActualAdapted
end
