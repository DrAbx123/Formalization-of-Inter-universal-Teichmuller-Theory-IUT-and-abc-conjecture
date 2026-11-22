import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceQSideComparison

/-! # S3131 instantiation attempt: SourceQSideComparison (q-side) -/

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S3131SourceQSideInstantiationAttemptActual

universe u

/-- REUSE: the consumer's `ENNReal.ofReal q` slot degenerates for q < 0. -/
theorem hqSlot_degenerate_reuse {X : Type u} (W : IQHullLogVolumeInterface X) {q : Real}
    (hqneg : q < 0) : ENNReal.ofReal q ≤ W.logVolume W.imageSet :=
  iqHullCertificate_hqSlot_of_neg W hqneg

def S3131QSideRemainingHypotheses : List String :=
  [ "paper-faithful q-side comparison must use sourceQSideNormalizedValue (signed real), not the ENNReal slot (degenerate per iqHullCertificate_hqSlot_of_neg)",
    "q-side comparison itself (q <= normalized theta log-volume) remains the named hypothesis; I-layer/Psi^cns carrier PARK; under degree faithfulness sourceHullVolume = top so no theta upper-bound slot",
    "our S3131QSideSignedComparisonHypothesis is the Lean-side named statement of the remaining comparison" ]

theorem S3131QSideRemainingHypotheses_length : S3131QSideRemainingHypotheses.length = 3 := rfl

#check iqHullCertificate_hqSlot_of_neg

end LeanFormal.IUT.XiFPaper.S3131SourceQSideInstantiationAttemptActual
end