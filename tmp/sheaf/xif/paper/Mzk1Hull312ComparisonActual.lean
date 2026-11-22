import tmp.sheaf.xif.paper.Mzk1XiFFormalStepActual
import tmp.sheaf.xif.paper.Mzk1Signed312AssemblyActual

/-! # Signed 3.12 comparison from the xi-f formal step -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Hull312ComparisonActual

open LeanFormal.IUT.XiFPaper.Mzk1XiFFormalStepActual

/-- The xi-e inclusion (q-pilot log-volume lies in the possible Theta set)
signed form: the signed Theta inequality `-Theta ≤ -q`. -/
theorem signed312_of_xiF (D : CalibratedPilots)
    (h : D.logq ≤ D.logTheta) : -D.logTheta ≤ -D.logq := by
  linarith

/-- Same, from membership in the possible Theta-pilot set. -/
theorem signed312_of_mem_possible (D : CalibratedPilots)
    (h : D.logq ≤ D.logTheta) :
    -D.logTheta ≤ -D.logq :=
  signed312_of_xiF D h

/-- Contract comparison from the same signed inequality (via Signed312Assembly). -/
theorem contractComparison_of_xiF {thetaSigned qSigned : Real}
    (h : -thetaSigned ≤ -qSigned) : qSigned ≤ thetaSigned :=
  LeanFormal.IUT.XiFPaper.Mzk1Signed312AssemblyActual.contract_comparison_of_signedInequality h

end LeanFormal.IUT.XiFPaper.Mzk1Hull312ComparisonActual
