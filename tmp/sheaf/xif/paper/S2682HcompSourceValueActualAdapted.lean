import tmp.sheaf.xif.paper.S1527OOrderEqualityActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2682HcompSourceValueActualAdapted

variable {l : PrimeGeFive}
variable (R : S1280RemainingClauses l)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop)
variable (hcusCompat : cusCompat)

/-- Actual source value: the S1280 bad q-family is (1/5)^order_C3, so its
total absolute log is order_C3 * log 5. -/
theorem S2682SourceBadQAbsLog_eq_order_mul_log :
    sourceBadQAbsLog
      (S1527SourceData l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat) =
      (S1527OrderC3 : Real) * Real.log 5 :=
  S1527_sourceBadQAbsLog l R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat

/-- The q-parameter value at the unique bad place when order_C3 = 1: 1/5. -/
theorem S2682QParameter_eq_inv_five_of_order_one
    (h : S1527OrderC3 = 1) (b : Bad (S1280Selection l)) :
    (S1280ReductionClause l).qParameter b = ((5 : Real)⁻¹) := by
  rw [S1280ReductionClause_qParameter_eq, S1527_badPlaceQCandidate_order_eq l b, h]
  norm_num

/-- If order_C3 = 1, the source bad q absolute log is exactly log 5. -/
theorem S2682SourceBadQAbsLog_eq_log5_of_order_one
    (h : S1527OrderC3 = 1) :
    sourceBadQAbsLog
      (S1527SourceData l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat) =
      Real.log 5 := by
  rw [S2682SourceBadQAbsLog_eq_order_mul_log (l := l) R redCompat hredCompat
    torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat
    hcusCompat, h]
  norm_num

/-- hcomp comparison condition: 2 log 5 ≤ sourceBadQAbsLog iff order_C3 ≥ 2. -/
theorem S2682TwoLog5_le_iff_two_le_order :
    (2 * Real.log 5 ≤ sourceBadQAbsLog
        (S1527SourceData l R redCompat hredCompat torCompat htorCompat
          orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)) ↔
      2 ≤ S1527OrderC3 := by
  rw [S2682SourceBadQAbsLog_eq_order_mul_log (l := l) R redCompat hredCompat
    torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat
    hcusCompat]
  have hlog5 : 0 < Real.log (5 : Real) :=
    Real.log_pos (by norm_num)
  constructor
  · intro h
    have h' : (2 : Real) * Real.log 5 ≤ (S1527OrderC3 : Real) * Real.log 5 := by
      simpa [mul_comm] using h
    have h2 : (2 : Real) ≤ (S1527OrderC3 : Real) :=
      le_of_mul_le_mul_right h' hlog5
    exact_mod_cast h2
  · intro h
    have h2 : (2 : Real) ≤ (S1527OrderC3 : Real) := by exact_mod_cast h
    calc
      (2 : Real) * Real.log 5 ≤ (S1527OrderC3 : Real) * Real.log 5 :=
        mul_le_mul_of_nonneg_right h2 (le_of_lt hlog5)
      _ = (S1527OrderC3 : Real) * Real.log 5 := rfl

/-- If order_C3 = 1, hcomp's 2 log 5 lower bound is false: source value is
log 5 < 2 log 5. -/
theorem S2682TwoLog5_false_of_order_one
    (h : S1527OrderC3 = 1) :
    ¬ (2 * Real.log 5 ≤ sourceBadQAbsLog
        (S1527SourceData l R redCompat hredCompat torCompat htorCompat
          orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)) := by
  rw [S2682SourceBadQAbsLog_eq_log5_of_order_one (l := l) R redCompat hredCompat
    torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat
    hcusCompat h]
  have hlog5 : 0 < Real.log (5 : Real) :=
    Real.log_pos (by norm_num)
  linarith

#print axioms S2682SourceBadQAbsLog_eq_order_mul_log
#print axioms S2682TwoLog5_le_iff_two_le_order
#print axioms S2682TwoLog5_false_of_order_one

end LeanFormal.IUT.XiFPaper.S2682HcompSourceValueActualAdapted
end
