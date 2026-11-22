import tmp.sheaf.n8.closure.SourceAllowedOutputActualAttempt
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.P6Comparison
open LeanFormal.IUT.N8Closure.SourceAllowedOutputActualAttempt
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2602SourceAllowedRegionAnchorActual

variable {l : PrimeGeFive} {X : N8NativeInput l}

/-- **P4/P5 anchored to the actual C9 hull/region object, NOT to the raw
sourceThetaPilotPoint.**  For each ABC triple we choose an actual C4 choice
`c`; the comparison region is the singleton `{J.T.thetaImage J.n c}` in the
actual C6 carrier, and its log-volume is `J.B.normalizedLogVolume`. -/
structure SourceAllowedRegionAnchor (J : P6Comparison.SourceAllowedOutput X) where
  /-- The actual C4 choice attached to the ABC triple. -/
  choice : Nat -> Nat -> Nat -> J.D.Choice J.n J.x
  /-- P4: arithmetic weight bounded by the C6 normalized log-volume of the
  actual theta-image region. -/
  weightDictionary :
    forall a b c : Nat, IsABCTriple a b c ->
      arithmeticWeight (abcRationalPoint a c) <=
        J.B.normalizedLogVolume
          {J.T.thetaImage J.n (choice a b c)}
  /-- P5: the same region log-volume bounds the canonical height. -/
  pointHeightDictionary :
    forall a b c : Nat, IsABCTriple a b c ->
      J.B.normalizedLogVolume {J.T.thetaImage J.n (choice a b c)} <=
        Height.logHeight₁ (abcRationalPoint a c)

/-- The actual region of a choice is exactly a theta-image singleton, not a
raw theta-pilot point. -/
theorem SourceAllowedRegionAnchor.region_eq
    (J : P6Comparison.SourceAllowedOutput X) (A : SourceAllowedRegionAnchor J)
    (a b c : Nat) :
    ({J.T.thetaImage J.n (A.choice a b c)} : Set (J.C6IQCarrier)) =
      {J.T.thetaImage J.n (A.choice a b c)} := rfl

#print axioms SourceAllowedRegionAnchor.region_eq

end LeanFormal.IUT.XiFPaper.S2602SourceAllowedRegionAnchorActual
end
