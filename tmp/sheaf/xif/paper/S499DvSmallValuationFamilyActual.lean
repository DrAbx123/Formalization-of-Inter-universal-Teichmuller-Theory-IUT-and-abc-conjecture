import tmp.sheaf.xif.paper.S495DvSmallValuationActual
import tmp.sheaf.xif.paper.S493Example32InputIsoActual
import tmp.sheaf.xif.paper.S468DivisorNaturalityActual

/-! # S499: DvSmallValuationFamily conditional construction / exact gap

The paper wants the normalized valuation of K extended to every finite etale
field cover L/K.  Mathlib has Valuation.HasExtension but no existence or
uniqueness theorem for the normalized extension of a complete DVR along a
finite separable field extension, and no ramification normalization formula.

This file aligns the conditional family with S493/S468 and records the exact
missing extension/uniqueness data.  No valuation is fabricated. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S499DvSmallValuationFamilyActual

open LeanFormal.IUT.XiFPaper.S495DvSmallValuationActual
open LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual
open LeanFormal.IUT.XiFPaper.S493Example32InputIsoActual
open LeanFormal.IUT.XiFPaper.S432SmallModelActual

universe u
variable (K : Type u) [Field K]

/-- S499 family type, definitionally the S468/S493 interface. -/
abbrev S499DvSmallValuationFamily : Type (u + 1) :=
  DvSmallValuationFamily (K := K)

/-- Conditional actual family from the exact existence hypothesis. -/
noncomputable def s499DvSmallValuationFamily
    (h : DvSmallValuationExtensionExists K) :
    S499DvSmallValuationFamily (K := K) :=
  dvSmallValuationFamilyOfExists (K := K) h

/-- The conditional family has the required componentwise value. -/
theorem s499DvSmallValuationFamily_apply
    (h : DvSmallValuationExtensionExists K) (X : Example32SmallBase K) :
    s499DvSmallValuationFamily (K := K) h X =
      Classical.choice (h X) := rfl

/-- Exact missing existence of the normalized extension. -/
def S499ValuationExtensionRequired : Prop :=
  DvSmallValuationExtensionExists K

/-- Exact missing uniqueness of the normalized extension. -/
def S499ValuationUniquenessRequired : Prop :=
  DvSmallValuationExtensionUnique K

/-- Exact qValuation normalization gap. -/
def S499QValuationRamificationRequired
    (ramificationIndex qOrder : Example32SmallBase K → ℤ) : Prop :=
  DvSmallQValuationEqRamificationMulOrder (K := K) ramificationIndex qOrder

/-- S499 data: a family plus S468 compatibility, aligned with S493's
valuationFamily field.  Both existence and compatibility are explicit. -/
structure S499AlignedValuationFamilyData where
  valuationFamily : DvSmallValuationFamily (K := K)
  compatibility : DvSmallValuationCompatibility (K := K) valuationFamily

/-- Conditional aligned package from the exact existence hypothesis plus S468
compatibility; no compatibility is derived here. -/
noncomputable def s499AlignedValuationFamilyData
    (h : DvSmallValuationExtensionExists K)
    (hc : DvSmallValuationCompatibility (K := K)
      (dvSmallValuationFamilyOfExists (K := K) h)) :
    S499AlignedValuationFamilyData (K := K) where
  valuationFamily := dvSmallValuationFamilyOfExists (K := K) h
  compatibility := hc

end LeanFormal.IUT.XiFPaper.S499DvSmallValuationFamilyActual

end
