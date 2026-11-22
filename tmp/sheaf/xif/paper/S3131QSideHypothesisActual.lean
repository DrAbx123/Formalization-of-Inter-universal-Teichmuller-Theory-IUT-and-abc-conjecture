import tmp.sheaf.xif.paper.S3131PaperRouteComparisonDataActual

/-! # S3131 route: q-side signed comparison as NAMED explicit hypothesis -/

noncomputable section
open LeanFormal.IUT.XiFPaper.S3131PaperRouteComparisonDataActual

namespace LeanFormal.IUT.XiFPaper.S3131QSideHypothesisActual

/-- NAMED q-side hypothesis: the signed q-pilot readout is <= the signed theta-hull
readout (with q-side sign convention qSigned < 0).  This is the explicit q-side
comparison hypothesis; it is NOT derived from qualitative data. -/
def S3131QSideSignedComparisonHypothesis (qSigned thetaSigned : Real) : Prop :=
  qSigned ≤ thetaSigned ∧ qSigned < 0

/-- From the named q-side hypothesis build the vendor-shaped comparison payload. -/
def payloadOfQSideHypothesis {qSigned thetaSigned : Real}
    (h : S3131QSideSignedComparisonHypothesis qSigned thetaSigned) :
    S3131PaperRouteComparisonData :=
  { thetaSigned := thetaSigned, qSigned := qSigned,
    q_positive := by linarith [h.2],
    qSigned_le_thetaSigned := h.1 }

/-- Cor. 3.12 magnitude endpoint from the named q-side hypothesis. -/
theorem magnitude_ofQSideHypothesis {qSigned thetaSigned : Real}
    (h : S3131QSideSignedComparisonHypothesis qSigned thetaSigned) :
    -thetaSigned ≤ -qSigned :=
  S3131PaperRouteComparisonData.magnitude_le (payloadOfQSideHypothesis h)

#check S3131QSideSignedComparisonHypothesis
#check magnitude_ofQSideHypothesis

end LeanFormal.IUT.XiFPaper.S3131QSideHypothesisActual
end