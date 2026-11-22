import tmp.sheaf.xif.paper.S2935HeightLeProcessionActual
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantHeight

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2935HeightLeProcessionActual
open LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
open LeanFormal.IUT.XiFPaper.S2933PerTripleThetaCertificateActual
open LeanFormal.IUT.XiFPaper.S2792NormalizedLineBundleBridge
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open Finset
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2941HeightUpperToProcessionAttempt

/-- The per-triple procession average appearing in S2935. -/
noncomputable def S2941ProcessionAverage (n a b c : Nat) : Real :=
  (1 / (n : Real)) *
    ∑ j ∈ Icc 1 n,
      collectionBound (2 * (n : Real) + 1) S2921D
        (S2921Q a b c) (S2921S a b c) (S2921T a b c) j

/-- The elementary ABC upper bound target: 6 log c + log 256 ≤ procession. -/
def S2941ElementaryTarget (n : Nat) : Prop :=
  ∀ a b c : Nat, IsABCTriple a b c →
    6 * Real.log (c : Real) + Real.log 256 ≤
      S2941ProcessionAverage n a b c

/-- Actual upper bound: J-height is at most 6 log c + log 256. -/
theorem S2941_Jheight_upper
    (a b c : Nat) (habc : IsABCTriple a b c) :
    Height.logHeight₁ (abcJInvariant a b c) ≤
      6 * Real.log (c : Real) + Real.log 256 :=
  abcJInvariant_logHeight_le habc

/-- The available lower bound on J-height: 6 log c + log(27/64) ≤ J-height. -/
theorem S2941_Jheight_lower
    (a b c : Nat) (habc : IsABCTriple a b c) :
    6 * Real.log (c : Real) + Real.log (27 / 64 : Real) ≤
      Height.logHeight₁ (abcJInvariant a b c) :=
  abcJInvariant_logHeight_ge habc

/-- Conditional consequence of height ≤ procession: the lower elementary
expression is bounded by the procession average. -/
theorem S2941_logc_lower_bound_of_height
    (n : Nat) (h : S2935HeightLeProcession n)
    (a b c : Nat) (habc : IsABCTriple a b c) :
    6 * Real.log (c : Real) + Real.log (27 / 64 : Real) ≤
      S2941ProcessionAverage n a b c := by
  have hge := S2941_Jheight_lower a b c habc
  have hle := h a b c habc
  exact le_trans hge hle

/-- The gap between the available lower bound and the desired upper bound is
strictly positive. -/
theorem S2941_log_gap_pos :
    Real.log (27 / 64 : Real) < Real.log 256 := by
  apply Real.log_lt_log
  · norm_num
  · norm_num

/-- The elementary target would give the J-height-to-procession inequality. -/
theorem S2941_heightLeProcession_of_elementary
    (n : Nat) (h : S2941ElementaryTarget n) :
    S2935HeightLeProcession n := by
  intro a b c habc
  exact le_trans (S2941_Jheight_upper a b c habc) (h a b c habc)

#check S2941ProcessionAverage
#check S2941ElementaryTarget
#check S2941_Jheight_upper
#check S2941_Jheight_lower
#check S2941_logc_lower_bound_of_height
#check S2941_log_gap_pos
#check S2941_heightLeProcession_of_elementary
#print axioms S2941_Jheight_upper
#print axioms S2941_Jheight_lower
#print axioms S2941_log_gap_pos
#print axioms S2941_heightLeProcession_of_elementary

end LeanFormal.IUT.XiFPaper.S2941HeightUpperToProcessionAttempt
end
