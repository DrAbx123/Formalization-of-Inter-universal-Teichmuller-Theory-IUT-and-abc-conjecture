import tmp.sheaf.xif.paper.Mzk1A618ScalingObstructionActual
import tmp.sheaf.xif.paper.Mzk1Stage4PaperComparisonRegionScalingDesignActual
import tmp.sheaf.xif.paper.Mzk1Stage4PaperRegionIdentityObstructionActual
import tmp.sheaf.xif.paper.Mzk1Stage4PaperRegionIdentityObstructionTInstanceActual

/-! # Mzk1Stage4A618ObstructionConsumerActual (stage4 lane; A618 consumer, supplemental)

A644 module: stage4 consumer of the canonical GREEN A618 machine proof —
`Mzk1A618ScalingObstructionActual.identity_scaleShift_obstruction` (unit-region form;
gate trio [propext, Classical.choice, Quot.sound]) is used as the ONLY source.
The old `Mzk1A618MachineProofActual.concreteS1902Interface_insufficient` is NOT used.
Canonical file only READ.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4A618ObstructionConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4PaperComparisonRegionScalingDesignActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4PaperRegionIdentityObstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4PaperRegionIdentityObstructionTInstanceActual
open Mzk1A618ScalingObstructionActual
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Stage4 consumer: the canonical A618 obstruction (unit-region form) — with the
actual hull interface (scaleShift = id) no height comparison can hold. -/
theorem stage4_identity_obstruction (epsilon : Real) :
    ¬ (∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * (s1902LogVolume T (s1902UnitRegion T)).toReal) :=
  identity_scaleShift_obstruction T epsilon

/-- Stage4 consumer in the identity-scaling region form: with identity scaling the
comparison region is the fixed `unit ∪ {point}` (so no triple dependence). -/
theorem stage4_identity_region (point : S1902Carrier T) (a b c a' b' c' : Nat) :
    region (identityScaling (S1902Carrier T) (s1902UnitRegion T) point) a b c =
      region (identityScaling (S1902Carrier T) (s1902UnitRegion T) point) a' b' c' :=
  s1902_identity_region_independent T point a b c a' b' c'

#print axioms stage4_identity_obstruction
#print axioms Mzk1A618ScalingObstructionActual.identity_scaleShift_obstruction

#check stage4_identity_obstruction
#check stage4_identity_region

end LeanFormal.IUT.XiFPaper.Mzk1Stage4A618ObstructionConsumerActual
end
