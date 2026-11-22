import tmp.sheaf.xif.paper.S1527OOrderEqualityActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S2683SingletonBadNormalizationAuditActual

universe u
variable {l : PrimeGeFive}

/-- Paper normalization for the S1280 singleton bad family: the bad-family
q-log sum, which S1527 computes as order_C3 * log 5. -/
noncomputable def S2683PaperSingletonNormalization : Real :=
  (S1527OrderC3 : Real) * Real.log 5

theorem S2683_sourceBadQAbsLog_eq
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    sourceBadQAbsLog
        (S1527SourceData l R redCompat hredCompat torCompat htorCompat orbCompat
          horbCompat secCompat hsecCompat cusCompat hcusCompat) =
      S2683PaperSingletonNormalization := by
  rw [S1527_sourceBadQAbsLog]
  rfl

theorem S2683_log5_ne_zero : Real.log (5 : Real) ≠ 0 :=
  ne_of_gt (Real.log_pos (by norm_num : (1 : Real) < 5))

/-- Exact comparison: the concrete Gaussian 2 log 5 equals the paper
singleton-bad normalization exactly when order_C3 = 2. -/
theorem S2683_two_log5_eq_normalization_iff :
    (2 : Real) * Real.log 5 = S2683PaperSingletonNormalization ↔
      S1527OrderC3 = 2 := by
  constructor
  · intro h
    have h' := congrArg (fun x : Real => x / Real.log 5) h
    simp only [S2683PaperSingletonNormalization, mul_div_cancel_right₀ _
      S2683_log5_ne_zero] at h'
    norm_num at h'
    exact_mod_cast h'.symm
  · intro h
    unfold S2683PaperSingletonNormalization
    rw [h]
    norm_num

/-- Exact mismatch criterion: if order_C3 ≠ 2, the concrete hull's 2 log 5
is not the paper singleton-bad normalization. -/
theorem S2683_two_log5_ne_normalization_of_order_ne_two
    (h : S1527OrderC3 ≠ 2) :
    (2 : Real) * Real.log 5 ≠ S2683PaperSingletonNormalization :=
  fun heq => h ((S2683_two_log5_eq_normalization_iff).mp heq)

#check S2683PaperSingletonNormalization
#check S2683_sourceBadQAbsLog_eq
#check S2683_two_log5_eq_normalization_iff
#check S2683_two_log5_ne_normalization_of_order_ne_two
#print axioms S2683_two_log5_eq_normalization_iff
end LeanFormal.IUT.XiFPaper.S2683SingletonBadNormalizationAuditActual
end