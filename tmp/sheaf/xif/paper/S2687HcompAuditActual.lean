import tmp.sheaf.xif.paper.S1527OOrderEqualityActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S2687HcompAuditActual

variable {l : PrimeGeFive}
variable (R : S1280RemainingClauses l)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)

/-- Actual paper q-side value for the S1280 bad family: order_C3 * log 5. -/
theorem S2687_sourceBadQAbsLog_eq :
    sourceBadQAbsLog
      (S1527SourceData l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat) =
      (S1527OrderC3 : Real) * Real.log 5 :=
  S1527_sourceBadQAbsLog l R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat

/-- hcomp comparison is exactly order_C3 ≥ 2. -/
theorem S2687_two_log5_le_sourceBadQ_iff_two_le_order :
    (2 * Real.log 5 ≤ sourceBadQAbsLog
      (S1527SourceData l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat)) ↔
      2 ≤ S1527OrderC3 := by
  rw [S2687_sourceBadQAbsLog_eq R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat]
  have hlog5 : 0 < Real.log (5 : Real) := Real.log_pos (by norm_num)
  constructor
  · intro h
    have h' : (2 : Real) * Real.log 5 ≤ (S1527OrderC3 : Real) * Real.log 5 := h
    have h2 : (2 : Real) ≤ (S1527OrderC3 : Real) :=
      (mul_le_mul_iff_of_pos_right hlog5).mp h'
    exact_mod_cast h2
  · intro h
    have h2 : (2 : Real) ≤ (S1527OrderC3 : Real) := by exact_mod_cast h
    exact mul_le_mul_of_nonneg_right h2 (le_of_lt hlog5)

/-- If order_C3 = 1, hcomp fails: source is log 5, below 2 log 5. -/
theorem S2687_hcomp_false_of_order_one
    (h : S1527OrderC3 = 1) :
    ¬ (2 * Real.log 5 ≤ sourceBadQAbsLog
      (S1527SourceData l R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat)) := by
  rw [S2687_sourceBadQAbsLog_eq R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat, h]
  have hlog5 : 0 < Real.log (5 : Real) := Real.log_pos (by norm_num)
  norm_num
  linarith

/-- Exact missing arithmetic input: the actual order is at least 2. -/
def S2687OrderAtLeastTwo : Prop := 2 ≤ S1527OrderC3

#check S2687_sourceBadQAbsLog_eq
#check S2687_two_log5_le_sourceBadQ_iff_two_le_order
#check S2687_hcomp_false_of_order_one
#check S2687OrderAtLeastTwo
#print axioms S2687_sourceBadQAbsLog_eq
#print axioms S2687_two_log5_le_sourceBadQ_iff_two_le_order
#print axioms S2687_hcomp_false_of_order_one

end LeanFormal.IUT.XiFPaper.S2687HcompAuditActual
end