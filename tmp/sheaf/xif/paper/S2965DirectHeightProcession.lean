import tmp.sheaf.xif.paper.S2941HeightUpperToProcessionAttempt
import tmp.sheaf.xif.paper.S2921HeightBridgeActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2941HeightUpperToProcessionAttempt
open LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open Finset
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2965DirectHeightProcession

def S2965Target (n : Nat) : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    6 * Real.log (c : Real) + Real.log 256 <=
      (1 / (n : Real)) *
        ∑ j ∈ Icc 1 n,
          collectionBound (2 * (n : Real) + 1) S2921D
            (S2921Q a b c) (S2921S a b c) (S2921T a b c) j

theorem S2965_target_iff_linear
    (n : Nat) (hn : 1 <= n) :
    S2965Target n <->
      forall a b c : Nat, IsABCTriple a b c ->
        6 * Real.log (c : Real) + Real.log 256 <=
          ((2 * (n : Real) + 1) + 5) / 4 * S2921D -
            ((2 * (n : Real) + 1) + 1) / 24 * S2921Q a b c +
            S2921S a b c + ((2 * (n : Real) + 1) + 5) * S2921T a b c := by
  constructor
  · intro h a b c habc
    have h1 := h a b c habc
    rw [processionAverage_eq n hn] at h1
    exact h1
  · intro h a b c habc
    have h1 := h a b c habc
    rw [processionAverage_eq n hn]
    exact h1

def S2965MinimalLinear (n : Nat) : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    6 * Real.log (c : Real) + Real.log 256 <=
      ((2 * (n : Real) + 1) + 5) / 4 * S2921D -
        ((2 * (n : Real) + 1) + 1) / 24 * S2921Q a b c +
        S2921S a b c + ((2 * (n : Real) + 1) + 5) * S2921T a b c

theorem S2965_target_of_minimal (n : Nat) (hn : 1 <= n)
    (h : S2965MinimalLinear n) : S2965Target n :=
  (S2965_target_iff_linear n hn).mpr h

theorem S2965_minimal_of_target (n : Nat) (hn : 1 <= n)
    (h : S2965Target n) : S2965MinimalLinear n :=
  (S2965_target_iff_linear n hn).mp h

#check S2965Target
#check S2965_target_iff_linear
#check S2965MinimalLinear
#check S2965_target_of_minimal
#check S2965_minimal_of_target
#print axioms S2965_target_iff_linear

end LeanFormal.IUT.XiFPaper.S2965DirectHeightProcession
end