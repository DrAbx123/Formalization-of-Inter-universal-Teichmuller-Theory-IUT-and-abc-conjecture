import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesShaActual

/-! # LANA IUT IV `LocalEstimate` interface consumer (gap correspondence)

Ported interface shape of LANA `Iut/Concrete/LocalEstimate.lean` (IUT IV Steps
(iv)-(vii)): the concrete local estimates consumed by Theorem 1.10 are represented by
their two gap components.  This file does not re-derive the local-field theory; it
provides the consumer/gap correspondence used by our ABC two-estimate assembly. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1LanaIutIVLocalEstimateConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual

/-- The two local estimates of IUT IV Step (v)/(vii), as a consumer-level package. -/
structure LocalEstimate
    (logVolume : Nat → Nat → Nat → Real) (hullVolume : Real) where
  height_estimate : forall δ : Real, 0 < δ → forall a b c : Nat,
    IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + δ) * logVolume a b c
  volume_estimate : forall δ : Real, 0 < δ → exists D : Real,
    forall a b c : Nat, IsABCTriple a b c →
      logVolume a b c ≤ (1 + δ) * arithmeticWeight (abcRationalPoint a c) +
        hullVolume + D

/-- Consumer: the local estimates assemble the ABC two-estimate package. -/
noncomputable def LocalEstimate.toTwoEstimates
    {logVolume : Nat → Nat → Nat → Real} {hullVolume : Real}
    (L : LocalEstimate logVolume hullVolume) : ABCTwoEstimates where
  logVolume := logVolume
  hullVolume := hullVolume
  height_estimate := L.height_estimate
  volume_estimate := L.volume_estimate

/-- Gap correspondence: the LANA local estimates imply `ABCConjecture`. -/
theorem abc_of_localEstimate
    {logVolume : Nat → Nat → Nat → Real} {hullVolume : Real}
    (L : LocalEstimate logVolume hullVolume) : ABCConjecture :=
  abc_of_twoEstimates (L.toTwoEstimates)

#print axioms abc_of_localEstimate

end LeanFormal.IUT.XiFPaper.Mzk1LanaIutIVLocalEstimateConsumerActual
