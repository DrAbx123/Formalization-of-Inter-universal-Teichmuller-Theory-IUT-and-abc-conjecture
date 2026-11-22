namespace LeanFormal.IUT.XiFPaper.Node09LogShellCardActual

/-- Exact remaining missing for the log-shell residue cardinal bridge.  The
bridge is not formalized in this file because importing the current
FinitePlaceCompletionLocalInputs chain still resolves a missing olean for the
moved module LeanFormal.IUT.Foundations.NumberField.FinitePlaceNormalizedCompletion,
even after the upstream chain was retouched and rebuilt. -/
def Node09LogShellCardRemainingMissing : List String :=
  [ "ResidueCardBridge: logShellResidueCard (K := Completion place) = Ideal.absNorm place.maximalIdeal.asIdeal",
    "planned proof route: Mathlib IsDedekindDomain.HeightOneSpectrum.adicCompletionResidueQuotientEquiv (residue field of adicCompletionIntegers equiv RingOfIntegers quotient) + Ideal.absNorm_apply",
    "persistent blocker: importing LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalInputs / FinitePlaceNormalizedCompletion still reports the missing olean LeanFormal.IUT.Foundations.NumberField.FinitePlaceNormalizedCompletion, even after rebuilding the four chain targets and IntegralLogShellIndexArithmetic/ResidueFormula to DONE",
    "downstream: once ResidueCardBridge holds, Fmod=Q gives localResidueDegree = actualFn by residueNormBase_eq_lower_pow + absNorm_rat_eq + Nat.pow_right_injective",
    "horder (qV order = 1) remains an explicit clause-B input; hbase needs PadicValuedCoherence (K := NativeBaseCompletionRaw)" ]

end LeanFormal.IUT.XiFPaper.Node09LogShellCardActual
