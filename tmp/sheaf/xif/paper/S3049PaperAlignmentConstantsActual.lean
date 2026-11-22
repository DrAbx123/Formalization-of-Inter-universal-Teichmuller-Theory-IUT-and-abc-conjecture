import tmp.sheaf.xif.paper.S3029StepVAlignmentActual
import tmp.sheaf.xif.paper.S2965MinimalAttemptActual
import tmp.sheaf.xif.paper.S3043LocalHaarVolumeSignActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3029StepVAlignmentActual
open LeanFormal.IUT.XiFPaper.S2965MinimalAttemptActual
open LeanFormal.IUT.XiFPaper.S2967QDecomposition
open LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
open Finset
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3049PaperAlignmentConstantsActual

/-- Actual coefficient cD from the S2965 reduction D = 0. -/
noncomputable def S3049CD (n : Nat) : Real := 0

/-- Actual coefficient cQ from the S2921 Q term. -/
noncomputable def S3049CQ (n : Nat) : Real :=
  -(((2 * (n : Real) + 1) + 1) / 24)

/-- Actual coefficient cS from the S2921 S term. -/
noncomputable def S3049CS (n : Nat) : Real := 1

/-- Actual coefficient cT from the S2921 T term. -/
noncomputable def S3049CT (n : Nat) : Real :=
  (2 * (n : Real) + 1) + 5

/-- Actual affine constant after substituting D = 0, Q = c0 + S, T = 5S. -/
noncomputable def S3049C0 (n : Nat) : Real :=
  -(((2 * (n : Real) + 1) + 1) / 24) * S2967QDecomposition.S2967Qconst

/-- Actual reduced coefficient of S after eliminating D, Q, T. -/
noncomputable def S3049SLowerCoeff (n : Nat) : Real :=
  1 - (((2 * (n : Real) + 1) + 1) / 24) +
    ((2 * (n : Real) + 1) + 5) * 5

/-- Exact reduction of the S2921 per-label linear expression to S and c0. -/
theorem S3049_perLabel_reduced (n a b c : Nat) :
    ((2 * (n : Real) + 1) + 5) / 4 * S2921D -
        ((2 * (n : Real) + 1) + 1) / 24 * S2921Q a b c +
        S2921S a b c + ((2 * (n : Real) + 1) + 5) * S2921T a b c =
      S3049C0 n + S3049SLowerCoeff n * S2921S a b c := by
  rw [S2965_D_eq_zero, S2965_Q_eq_const_add_S a b c,
    S2965_T_eq_five_mul_S a b c]
  unfold S3049C0 S3049SLowerCoeff
  ring

#check S3049CD
#check S3049CQ
#check S3049CS
#check S3049CT
#check S3049C0
#check S3049SLowerCoeff
#check S3049_perLabel_reduced
#print axioms S3049_perLabel_reduced

end LeanFormal.IUT.XiFPaper.S3049PaperAlignmentConstantsActual
end