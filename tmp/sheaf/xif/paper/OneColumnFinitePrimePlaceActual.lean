import LeanFormal.IUT.IUTIII.Theorem311.SourceArithmeticHolomorphicLanding
import LeanFormal.IUT.ABCBridge.Geometry.FreyTateAnalyticInput

/-!
# Actual 1-column arithmetic holomorphic structure on FinitePrimePlace 2 7

This file constructs the actual SourceOneColumnArithmeticHolomorphicStructure
on the finite prime places FinitePrimePlace 2 7.

For each v : FinitePrimePlace 2 7, v.1 is a rational prime.  The actual rational
finite place of Q at v.1 is rationalFinitePlace v.1 (FreyTateAnalyticInput),
and the local data are:

  localRing v  := NumberFieldFinitePlace.CompletionIntegers (rationalFinitePlace v.1)
  localField v := NumberFieldFinitePlace.Completion (rationalFinitePlace v.1)
  localizationInclusion v := ValuationSubring.subtype
                              (CompletionIntegers (rationalFinitePlace v.1))

Thus the local ring is the adic completion integers of Q at the rational prime,
the local field is the corresponding completion, and the localization inclusion
is the actual valuation-subring inclusion.  No Z/Q gate witness is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

/-- The actual rational finite place of Q associated to a finite prime place. -/
noncomputable def finitePrimePlaceToQ (v : FinitePrimePlace 2 7) :
    NumberField.FinitePlace ℚ :=
  letI : Fact (Nat.Prime v.1) := ⟨v.2.2.2⟩
  rationalFinitePlace v.1

/-- The actual local ring: completed valuation integers of Q at the rational
prime. -/
noncomputable abbrev actualLocalRing (v : FinitePrimePlace 2 7) : Type :=
  NumberFieldFinitePlace.CompletionIntegers (finitePrimePlaceToQ v)

/-- The actual local field: completion of Q at the rational prime. -/
noncomputable abbrev actualLocalField (v : FinitePrimePlace 2 7) : Type :=
  NumberFieldFinitePlace.Completion (finitePrimePlaceToQ v)

/-- The actual localization inclusion: valuation subring inclusion. -/
noncomputable def actualLocalizationInclusion (v : FinitePrimePlace 2 7) :
    actualLocalRing v →+* actualLocalField v := by
  letI : Fact (Nat.Prime v.1) := ⟨v.2.2.2⟩
  exact ValuationSubring.subtype
    (NumberFieldFinitePlace.CompletionIntegers (finitePrimePlaceToQ v))

/-- The actual one-column arithmetic holomorphic structure on FinitePrimePlace 2 7. -/
noncomputable def actualOneColumnFinitePrimePlace :
    SourceOneColumnArithmeticHolomorphicStructure (FinitePrimePlace 2 7) where
  localRing := fun v => NumberFieldFinitePlace.CompletionIntegers
    (finitePrimePlaceToQ v)
  ringOf := fun v => by
    letI : Fact (Nat.Prime v.1) := ⟨v.2.2.2⟩
    infer_instance
  localField := fun v => NumberFieldFinitePlace.Completion
    (finitePrimePlaceToQ v)
  fieldOf := fun v => by
    letI : Fact (Nat.Prime v.1) := ⟨v.2.2.2⟩
    infer_instance
  localizationInclusion := fun v => by
    letI : Fact (Nat.Prime v.1) := ⟨v.2.2.2⟩
    exact ValuationSubring.subtype
      (NumberFieldFinitePlace.CompletionIntegers (finitePrimePlaceToQ v))

/-- The local ring is exactly the completed valuation integers. -/
@[simp] theorem actualOneColumnFinitePrimePlace_localRing
    (v : FinitePrimePlace 2 7) :
    (actualOneColumnFinitePrimePlace).localRing v =
      NumberFieldFinitePlace.CompletionIntegers (finitePrimePlaceToQ v) := rfl

/-- The local field is exactly the rational completion. -/
@[simp] theorem actualOneColumnFinitePrimePlace_localField
    (v : FinitePrimePlace 2 7) :
    (actualOneColumnFinitePrimePlace).localField v =
      NumberFieldFinitePlace.Completion (finitePrimePlaceToQ v) := rfl

/-- The localization inclusion is the actual valuation-subring inclusion. -/
@[simp] theorem actualOneColumnFinitePrimePlace_localizationInclusion
    (v : FinitePrimePlace 2 7) :
    (actualOneColumnFinitePrimePlace).localizationInclusion v =
      actualLocalizationInclusion v := rfl

/-- The actual structure's localization inclusion is unital. -/
theorem actualLocalizationInclusion_one (v : FinitePrimePlace 2 7) :
    actualLocalizationInclusion v 1 = 1 :=
  (actualLocalizationInclusion v).map_one

/-- The actual structure's localization inclusion is multiplicative. -/
theorem actualLocalizationInclusion_mul (v : FinitePrimePlace 2 7)
    (x y : actualLocalRing v) :
    actualLocalizationInclusion v (x * y) =
      actualLocalizationInclusion v x * actualLocalizationInclusion v y :=
  (actualLocalizationInclusion v).map_mul x y

end LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual

end