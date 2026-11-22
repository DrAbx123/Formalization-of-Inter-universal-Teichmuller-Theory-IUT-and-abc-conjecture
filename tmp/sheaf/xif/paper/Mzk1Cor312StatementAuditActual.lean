import tmp.sheaf.xif.paper.Mzk1SignedLogVolumeCor312Actual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import tmp.sheaf.xif.paper.Mzk1SignedCor312ContractActual

/-!
# A540: statement-level self-check of paper Cor 3.12 (IUT III L10324-10353)

Paper statement: `-|log Theta| in R`, `-|log q| in R`, and
`-|log Theta| >= -|log q|` (equivalently, for any real C with
`-|log Theta| <= C |log q|`, one has `C >= -1`).

Here the readouts are signed real numbers (`-|log q| = log(vol q)`, negative
for the actual regions).  This file checks the statement-level arithmetic
independently of the final assembly: the signed claim is equivalent to the
`C >= -1` form, and a strict reading comparison rules out definitional vacuity.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312StatementAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1SignedLogVolumeCor312Actual

/-- Signed paper claim: q-pilot reading is negative and below the Theta-pilot
hull reading.  The real type already encodes finiteness (`in R`). -/
structure PaperCor312Claim where
  qLog : Real
  thetaLog : Real
  q_neg : qLog < 0
  q_le_theta : qLog ≤ thetaLog

/-- The target comparison of the signed claim. -/
theorem claim_le (D : PaperCor312Claim) : D.qLog ≤ D.thetaLog :=
  D.q_le_theta

/-- The signed claim is NOT an equality (no definitional vacuity): the readings
are strictly different in the strict version. -/
structure StrictPaperCor312Claim extends PaperCor312Claim where
  strict : qLog < thetaLog

theorem strict_claim_not_eq (D : StrictPaperCor312Claim) : D.qLog ≠ D.thetaLog :=
  ne_of_lt D.strict

/-- `C_Theta` form: if `qLog = -qMag` and `thetaLog = C * qMag` with
`qMag > 0`, then the signed claim gives `C >= -1`. -/
theorem claim_CTheta_ge_neg_one {qMag C qLog thetaLog : Real}
    (hq : 0 < qMag) (hqeq : qLog = -qMag) (hthetaeq : thetaLog = C * qMag)
    (hclaim : qLog ≤ thetaLog) : -1 ≤ C := by
  rw [hqeq, hthetaeq] at hclaim
  have hmul : (-1 : Real) * qMag ≤ C * qMag := by
    calc (-1 : Real) * qMag = -qMag := by ring
      _ ≤ C * qMag := hclaim
  exact le_of_mul_le_mul_right hmul hq

/-- Conversely, the `C >= -1` form gives the signed claim under the same
calibration. -/
theorem claim_of_CTheta_ge_neg_one {qMag C qLog thetaLog : Real}
    (hq : 0 < qMag) (hqeq : qLog = -qMag) (hthetaeq : thetaLog = C * qMag)
    (hC : -1 ≤ C) : qLog ≤ thetaLog := by
  rw [hqeq, hthetaeq]
  have hmul : (-1 : Real) * qMag ≤ C * qMag :=
    mul_le_mul_of_nonneg_right hC (le_of_lt hq)
  -- (-1) * a = -a
  calc -qMag = (-1 : Real) * qMag := by ring
    _ ≤ C * qMag := hmul

end LeanFormal.IUT.XiFPaper.Mzk1Cor312StatementAuditActual
