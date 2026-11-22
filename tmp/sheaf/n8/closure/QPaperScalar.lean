import tmp.sheaf.n8.closure.SourcePilotRegion
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

/-!
# C9 paper q scalar from the actual C3 q candidate

Source-compatible q-pilot signed scalar: `localSignedLog C3.q`.
This is only the scalar endpoint; the q-pilot region/log-volume donor remains open.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C9QPaper

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.ArithmeticQPilotLogVolume

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : Theorem311Source.OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- Actual signed q scalar from the C3 completion q. -/
noncomputable def qPaperScalar : ℝ :=
  localSignedLog C3.q

theorem qPaperScalar_eq :
    qPaperScalar C3 = Real.log ‖C3.q.q‖ := rfl

theorem qPaperScalar_neg : qPaperScalar C3 < 0 :=
  localSignedLog_neg C3.q

theorem qPaperScalar_eq_neg_magnitude :
    qPaperScalar C3 = -localLogMagnitude C3.q := by
  simp [qPaperScalar, localSignedLog_eq_neg_magnitude]

theorem qPaperScalar_abs :
    |qPaperScalar C3| = localLogMagnitude C3.q := by
  simp [qPaperScalar, abs_localSignedLog]

end LeanFormal.IUT.N8Closure.C9QPaper