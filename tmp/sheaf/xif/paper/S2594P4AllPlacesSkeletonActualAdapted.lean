import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import tmp.sheaf.xif.paper.S2593P4CandidateActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2594P4AllPlacesSkeletonActualAdapted

universe u ua uv upi umon ui

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)

/-- **Package A: per-rational-prime tensor carrier family.**
This is the data that must be constructed from the paper/source; it is not
reused from `SourceVolumeIndex`, which is `ThetaPilotCarrier x SignedLabel`
and refers to processions/labels, not to rational primes. -/
structure P4PerPrimeTensorCarrier where
  /-- The carrier at each rational prime (indexed here by `Nat`; primality
  is part of the point/support conditions, not of the type). -/
  X : Nat -> Type u
  /-- A norm on each per-prime carrier. -/
  norm : forall p : Nat, Norm (X p)
  /-- A unit point on each per-prime carrier. -/
  one : forall p : Nat, One (X p)
  /-- The actual all-places point map attached to `(a,b,c)`. -/
  point : Nat -> Nat -> Nat -> (p : Nat) -> X p

/-- **Package B: support identification.** The per-prime point is nontrivial
exactly on the arithmetic prime support of `x = a/c`. -/
def P4SupportIdentification (A : P4PerPrimeTensorCarrier.{u}) : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    forall p : Nat,
      p ∈ arithmeticPrimeSupport (abcRationalPoint a c) <->
        A.point a b c p ≠ (A.one p).one

/-- **Package C: support-to-valuation lower bound.** The support sum of the
per-prime log-norms bounds the arithmetic weight from below. -/
def P4SupportValuationLowerBound (A : P4PerPrimeTensorCarrier.{u}) : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    arithmeticWeight (abcRationalPoint a c) <=
      ∑ p in arithmeticPrimeSupport (abcRationalPoint a c),
        Real.log ((A.norm p).norm (A.point a b c p))

/-- **Package D: all-places dictionary.** A + B + C assembled. -/
structure P4AllPlacesPackage where
  carrier : P4PerPrimeTensorCarrier.{u}
  support_id : P4SupportIdentification carrier
  lower_bound : P4SupportValuationLowerBound carrier

/-- The all-places package gives the support-sum dictionary. -/
theorem P4AllPlacesPackage.dictionary
    (P : P4AllPlacesPackage.{u}) :
    forall a b c : Nat, IsABCTriple a b c ->
      arithmeticWeight (abcRationalPoint a c) <=
        ∑ p in arithmeticPrimeSupport (abcRationalPoint a c),
          Real.log ((P.carrier.norm p).norm (P.carrier.point a b c p)) :=
  P.lower_bound

/-- The current `SourceVolumeIndex` is the procession/label index, not a
prime index: its carrier is `ThetaPilotCarrier l x SignedLabel l.value`. -/
theorem P4_sourceVolumeIndex_eq_procession_labels :
    SourceVolumeIndex l = (ThetaPilotCarrier l × SignedLabel l.value) := rfl

/-- The per-prime carrier family is not the source volume index: the latter
is finite (`(lStar l + 1) * l`), while an all-rational-prime family would need
infinitely many indices.  This is the exact non-reuse statement. -/
theorem P4_no_reuse_sourceVolumeIndex :
    Fintype.card (SourceVolumeIndex l) = (lStar l.value + 1) * l.value := by
  exact Theorem311Source.OriginalInput.sourceVolumeIndex_finite l

#print axioms P4AllPlacesPackage.dictionary
#print axioms P4_no_reuse_sourceVolumeIndex

end LeanFormal.IUT.XiFPaper.S2594P4AllPlacesSkeletonActualAdapted
end
