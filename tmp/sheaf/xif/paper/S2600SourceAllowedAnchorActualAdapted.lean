import tmp.sheaf.n8.closure.SourceAllowedOutputActualAttempt
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.P6Comparison
open LeanFormal.IUT.N8Closure.SourceAllowedOutputActualAttempt
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2600SourceAllowedAnchorActualAdapted

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} {X : N8NativeInput l}

/-- **P4/P5 anchor on the actual C9 SourceAllowedOutput.**
The carrier is the `OriginalInput` of the output's bridge, the place is the
C4 place `J.D.place.v`, and the source state is the actual output state `J.x`.
The point map and the two dictionaries are the remaining numeric data; they
are anchored to the actual `J` and its actual `n`/`x`, not to an S2593
single-bad-place tensor block. -/
structure SourceAllowedP4P5Anchor (J : P6Comparison.SourceAllowedOutput X) where
  /-- The rational-point point map into the actual global theta-pilot carrier. -/
  point : Nat -> Nat -> Nat -> J.bridge.input.ThetaPilotPoint J.D.place.v
  /-- The P4 weight/source-log-degree dictionary at the actual global carrier. -/
  weightDictionary :
    forall a b c : Nat, IsABCTriple a b c ->
      arithmeticWeight (abcRationalPoint a c) <=
        J.bridge.input.sourceLocalLogDegree J.D.place.v (point a b c)
  /-- The P5 point-height dictionary at the actual global carrier. -/
  pointHeightDictionary :
    forall a b c : Nat, IsABCTriple a b c ->
      (J.bridge.input.sourceSetVolume J.D.place.v {point a b c}).toReal <=
        Height.logHeight₁ (abcRationalPoint a c)

/-- Actual anchor constructor from the C9 actual data package: J is the actual
`sourceAllowedOutputOfActualData A`; n and x are its actual fields. -/
noncomputable def sourceAllowedP4P5AnchorOfData
    (A : SourceAllowedActualData X)
    (point : Nat -> Nat -> Nat ->
      (sourceAllowedOutputOfActualData A).bridge.input.ThetaPilotPoint
        (sourceAllowedOutputOfActualData A).D.place.v)
    (hweight : forall a b c : Nat, IsABCTriple a b c ->
      arithmeticWeight (abcRationalPoint a c) <=
        (sourceAllowedOutputOfActualData A).bridge.input.sourceLocalLogDegree
          (sourceAllowedOutputOfActualData A).D.place.v (point a b c))
    (hpoint : forall a b c : Nat, IsABCTriple a b c ->
      ((sourceAllowedOutputOfActualData A).bridge.input.sourceSetVolume
        (sourceAllowedOutputOfActualData A).D.place.v {point a b c}).toReal <=
        Height.logHeight₁ (abcRationalPoint a c)) :
    SourceAllowedP4P5Anchor (sourceAllowedOutputOfActualData A) where
  point := point
  weightDictionary := hweight
  pointHeightDictionary := hpoint

/-- The anchor's actual processions index is the C9 output's actual `n`. -/
theorem sourceAllowedP4P5Anchor_n
    (A : SourceAllowedActualData X)
    (point : ...)
    (hweight : ...) (hpoint : ...) :
    (sourceAllowedP4P5AnchorOfData A point hweight hpoint).1 =
      (sourceAllowedOutputOfActualData A).n := rfl

#print axioms sourceAllowedP4P5AnchorOfData

end LeanFormal.IUT.XiFPaper.S2600SourceAllowedAnchorActualAdapted
end
