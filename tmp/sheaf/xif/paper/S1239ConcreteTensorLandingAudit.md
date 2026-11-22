# S1239: concrete TensorLanding/insertion donor audit

Date: 2026-10-30. Actual minimal donor + exact unit gap.

## Files read

* S1213-c3-donor-tensorlanding-audit.md (report-only);
* S1219ConcreteTensorLandingActual.lean (now fixed EXIT=0);
* BaseTensorInsertionActual.lean (read);
* ConcreteC3DonorCompletionActual / ConcreteC3RootTensorActual types (read).

## Actual minimal donor (S1219, EXIT=0)

For arbitrary
  I : OriginalInput.{0,0,upi,umon,ui} l (FinitePrimePlace 2 7)
and actual place : FinitePlaceAtPrime I.initial.arithmetic.Fmod p:

  ConcreteIndex := FinitePrimePlace 2 7
  concretePlaces i _ := place
  ConcreteBlock := ArithmeticTensorTupleBlock concretePlaces concreteTuple
  concreteTensorLanding z := finitePadicTensorTprod (fun _ => z)

The actual diagonal nonzero theorem is proved:

  finitePadicTensorTprod_diagonal_ne_zero :
    (hz : z != 0) -> finitePadicTensorTprod (fun _ => z) != 0

using finitePadicTensorCoordinates_tprod and a chosen nonzero coordinate for a
finite index, hence

  concreteTensorLanding_ne_zero : q.q != 0 -> concreteTensorLanding q.q != 0.

This is the minimal actual insertion/landing donor: an actual
CommonPrimeCompletion -> ConcreteBlock map and nonzero q landing.

## Exact gap: tensorUnit

ConcreteTensorLandingData / ConcreteC3DonorMissingFields.tensorLanding also need

  tensorUnit : (ConcreteBlock I place)^x

with a GroupWithZero/Units structure on ConcreteBlock.  The actual tensor block
carries AddCommGroup/Module but no GroupWithZero (it is a tensor product, not a
field), so Units.mk0 is not available.  S1213's proposed
tensorUnitInsertion := Units.mk0 (concreteInsertion q) nonzero is therefore
not constructible at this type as written.

The q-law tensorLanding q = tensorUnit cannot be stated until tensorUnit is
actually constructed.  Forcing it with an arbitrary unit/if-then would be a
fake landing and is not done.

## Consumer

ConcreteC3DonorMissingFields.tensorLanding (C3 donor assembly), downstream
SourceHDDReadout dsc -> hull+det.  The minimal donor reduces the consumer to the
actual landing map + nonzero proof; the unit field remains exact.

## Status

S1219 EXIT=0.  No weak Prop/Nonempty gate/arbitrary unit added.
