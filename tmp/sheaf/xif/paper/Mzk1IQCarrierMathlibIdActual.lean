/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1RestrictedProductReuseActual
import Mathlib.Tactic

/-! # P7/#2: IQ restricted-product carrier identified with Mathlib `Πʳ` -/

/-
| field | value |
|---|---|
| Status | PROVED type-identity: `IQRestrictedProductCarrier ι K O = (Πʳ i, [K i, O i])` (rfl), and coercion membership |
| GAP | GAP-P7-IQ-LITERAL: literal paper IQ paper identification remains; FLT FiniteAdeleRing currently blocked (Equiv.olean missing) |
-/

noncomputable section

open scoped RestrictedProduct

namespace LeanFormal.IUT.XiFPaper.Mzk1IQCarrierMathlibIdActual

open LeanFormal.IUT.XiFPaper.Mzk1RestrictedProductReuseActual

/-- The IQ skeleton is definitionally the Mathlib restricted product. -/
theorem IQRestrictedProductCarrier_eq
    (ι : Type*) (K : ι → Type*) (O : (i : ι) → Set (K i)) :
    IQRestrictedProductCarrier ι K O = (Πʳ i, [K i, O i]) := rfl

/-- Membership/coercion form of the identification. -/
theorem IQRestrictedProductCarrier_coe_mem
    {ι : Type*} {K : ι → Type*} {O : (i : ι) → Set (K i)}
    (x : IQRestrictedProductCarrier ι K O) :
    ∀ᶠ i in Filter.cofinite, x.1 i ∈ O i := x.2

end LeanFormal.IUT.XiFPaper.Mzk1IQCarrierMathlibIdActual