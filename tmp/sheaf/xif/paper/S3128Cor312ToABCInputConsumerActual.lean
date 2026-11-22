import LeanFormal.IUT.ABCBridge.Statement
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S3128Cor312ToABCInputConsumerActual

universe u

/-- Explicit input of the Corollary 3.12 -> ABC bridge.

This is a transparent restatement of the fields of
`Cor312ToABCBridgeInterface`: an ambient carrier with the paper-level hull
log-volume interface, plus the per-epsilon arithmetic comparison data
(with the two named, still-unproved comparison gaps).

It is an INPUT, not a proof of ABC: no unconditional `ABCConjecture` is
claimed anywhere in this file. -/
structure S3128Cor312ToABCInput where
  carrier : Type u
  hullData : IQHullLogVolumeInterface carrier
  epsilonComparison : ∀ epsilon : Real, 0 < epsilon →
    Cor312EpsilonArithmeticComparison hullData epsilon

/-- Regard the explicit input as the frozen bridge interface. -/
def S3128Cor312ToABCInput.toBridge (D : S3128Cor312ToABCInput.{u}) :
    Cor312ToABCBridgeInterface.{u} where
  carrier := D.carrier
  hullData := D.hullData
  epsilonComparison := D.epsilonComparison

/-- Conversely, any bridge interface inhabitant is an explicit input. -/
def S3128Cor312ToABCInput.ofBridge (D : Cor312ToABCBridgeInterface.{u}) :
    S3128Cor312ToABCInput.{u} where
  carrier := D.carrier
  hullData := D.hullData
  epsilonComparison := D.epsilonComparison

/-- Conditional consumer: the input yields the ABC-style height bound in the
exact form of the right-hand side of
`abcConjecture_iff_abcArithmeticWeightHeightBound`. -/
theorem S3128Cor312ToABCInput_heightBound
    (D : S3128Cor312ToABCInput.{u}) :
    ∀ epsilon : Real, 0 < epsilon → ∃ A : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  cor312ToABCBridge_heightBound D.toBridge

/-- Conditional consumer: the explicit input yields `ABCConjecture`. -/
theorem S3128Cor312ToABCInput_abcConjecture
    (D : S3128Cor312ToABCInput.{u}) : ABCConjecture :=
  cor312ToABCBridgeInterface_abcConjecture_of_nonempty ⟨D.toBridge⟩

/-- Strength calibration: the explicit input is inhabited exactly when ABC
holds; this is an equivalence, not an unconditional proof of ABC. -/
theorem S3128Cor312ToABCInput_nonempty_iff_abcConjecture :
    Nonempty S3128Cor312ToABCInput.{0} ↔ ABCConjecture :=
  ⟨fun h => S3128Cor312ToABCInput_abcConjecture h.some,
   fun h => ⟨S3128Cor312ToABCInput.ofBridge (cor312ToABCBridgeInterface_nonempty_of_abcConjecture h).some⟩⟩

#check S3128Cor312ToABCInput
#check S3128Cor312ToABCInput.toBridge
#check S3128Cor312ToABCInput.ofBridge
#check S3128Cor312ToABCInput_heightBound
#check S3128Cor312ToABCInput_abcConjecture
#check S3128Cor312ToABCInput_nonempty_iff_abcConjecture

end LeanFormal.IUT.XiFPaper.S3128Cor312ToABCInputConsumerActual
end