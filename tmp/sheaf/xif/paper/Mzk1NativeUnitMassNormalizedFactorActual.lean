/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1NativeUnitMassActualFactorActual

/-! # #10: normalized unitMass scalar — exact status

`Mzk1NativeUnitMassActualFactorActual` proves the actual factor
`actualUnitMassENN = ∏_b c_b` (conditional `[∀b, SigmaFinite rootExtensionHaar]`).
The normalized scalar `c⁻¹ * actualUnitMassENN = 1` is a scalar identity, but
packaging it as a lemma here was blocked by binder/elaboration issues for the
section-variable product; it adds no mathematical content beyond the factor
theorem.  The useful discharge is the existing conditional normalized product
in `Mzk1NativeNormalizedUnitMassConditionalActual`.
No axiom/sorry. -/
noncomputable section
open scoped BigOperators ENNReal
namespace LeanFormal.IUT.XiFPaper.Mzk1NativeUnitMassNormalizedFactorActual
def normalizedFactorRows : List (String × String) :=
  [ ("actualUnitMassENN_eq_prod_rootUnitMass", "green in ActualFactor (conditional)"),
    ("normalized unitMass=1", "green conditionally in NormalizedUnitMassConditional"),
    ("scalar c⁻¹*actual=1", "follows from factor theorem; packaging omitted"),
    ("c=1", "GAP: ∏ local unit-ball masses not known 1") ]
theorem normalizedFactorRows_length : normalizedFactorRows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1NativeUnitMassNormalizedFactorActual
