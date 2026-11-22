import tmp.sheaf.xif.paper.S2941HeightUpperToProcessionAttempt
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantHeight
import tmp.sheaf.xif.paper.S2936HeightBridgeAttemptActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2941HeightUpperToProcessionAttempt
open LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
open LeanFormal.IUT.XiFPaper.S2935HeightLeProcessionActual
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open LeanFormal.IUT.XiFPaper.S2936HeightBridgeAttemptActual
open Finset
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2946ElementaryTargetAttempt

theorem S2946_processionAverage_eq
    (n : Nat) (hn : 1 <= n) (a b c : Nat) :
    S2941ProcessionAverage n a b c =
      (((2 * (n : Real) + 1) + 5) / 4 * S2921D -
        ((2 * (n : Real) + 1) + 1) / 24 * S2921Q a b c +
        S2921S a b c + ((2 * (n : Real) + 1) + 5) * S2921T a b c) := by
  unfold S2941ProcessionAverage
  exact processionAverage_eq n hn S2921D (S2921Q a b c)
    (S2921S a b c) (S2921T a b c)

theorem S2946_processionAverage_le_weight
    (n : Nat) (a b c : Nat) (habc : IsABCTriple a b c) :
    S2941ProcessionAverage n a b c <=
      (1 / (n : Real)) *
        ∑ j ∈ Icc 1 n,
          collectionBound (2 * (n : Real) + 1) S2921D
            (arithmeticWeight (abcRationalPoint a c))
            (S2921S a b c) (S2921T a b c) j := by
  unfold S2941ProcessionAverage
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sum_le_sum
  intro j hj
  apply S2936_collectionBound_antitone_Q
  · positivity
  · exact S2921_hweightvol_candidate a b c habc

theorem S2946_target_iff_linear
    (n : Nat) (hn : 1 <= n) :
    S2941ElementaryTarget n ↔
      ∀ a b c : Nat, IsABCTriple a b c →
        6 * Real.log (c : Real) + Real.log 256 <=
          (((2 * (n : Real) + 1) + 5) / 4 * S2921D -
            ((2 * (n : Real) + 1) + 1) / 24 * S2921Q a b c +
            S2921S a b c + ((2 * (n : Real) + 1) + 5) * S2921T a b c) := by
  constructor
  · intro h a b c habc
    rw [← S2946_processionAverage_eq n hn a b c]
    exact h a b c habc
  · intro h a b c habc
    rw [S2946_processionAverage_eq n hn a b c]
    exact h a b c habc

theorem S2946_target_weight_form
    (n : Nat) (h : S2941ElementaryTarget n)
    (a b c : Nat) (habc : IsABCTriple a b c) :
    6 * Real.log (c : Real) + Real.log 256 <=
      (1 / (n : Real)) *
        ∑ j ∈ Icc 1 n,
          collectionBound (2 * (n : Real) + 1) S2921D
            (arithmeticWeight (abcRationalPoint a c))
            (S2921S a b c) (S2921T a b c) j :=
  le_trans (h a b c habc) (S2946_processionAverage_le_weight n a b c habc)

#check S2946_processionAverage_eq
#check S2946_processionAverage_le_weight
#check S2946_target_iff_linear
#check S2946_target_weight_form
#print axioms S2946_processionAverage_eq
#print axioms S2946_processionAverage_le_weight
#print axioms S2946_target_iff_linear
#print axioms S2946_target_weight_form

end LeanFormal.IUT.XiFPaper.S2946ElementaryTargetAttempt
end