/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Tactic

/-! # P7/#2: restricted product reuse (Mathlib) for the IQ carrier skeleton -/

/-
| field | value |
|---|---|
| Status | reuse: Mathlib already has `RestrictedProduct` (`Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean:79`, notation `Πʳ i, [R i, A i]_[𝓕]`); the FLT port is not needed |
| Reuse | `RestrictedProduct` def :79; `mk` :105; `ext` :113; `inclusion` :139; `structureMap` :129; topological space in `TopologicalSpace.lean` |
| GAP | GAP-P7-IQ-LITERAL: a restricted product skeleton is available, but the literal paper IQ(S±; n, D^vdash) carrier inhabitant/identification is still missing |
-/

noncomputable section

open scoped RestrictedProduct

namespace LeanFormal.IUT.XiFPaper.Mzk1RestrictedProductReuseActual

open RestrictedProduct

/-- **Membership characterization** of a Mathlib restricted product: the subtype
condition is exactly eventual membership. -/
theorem restrictedProduct_coe_mem
    {ι : Type*} {R : ι → Type*} {A : (i : ι) → Set (R i)} {𝓕 : Filter ι}
    (x : Πʳ i, [R i, A i]_[𝓕]) :
    ∀ᶠ i in 𝓕, x.1 i ∈ A i :=
  x.2

/-- The cofinite (classical) restricted product: all but finitely many coordinates
lie in the local subsets. -/
theorem restrictedProduct_coe_mem_cofinite
    {ι : Type*} {R : ι → Type*} {A : (i : ι) → Set (R i)}
    (x : Πʳ i, [R i, A i]) :
    ∀ᶠ i in Filter.cofinite, x.1 i ∈ A i :=
  x.2

/-- **IQ carrier skeleton**: the restricted product of local completed fields with
their integral (log-shell) subsets.  This is only the carrier skeleton; the paper's
literal IQ identification remains GAP-P7-IQ-LITERAL. -/
def IQRestrictedProductCarrier
    (ι : Type*) (K : ι → Type*) (O : (i : ι) → Set (K i)) : Type _ :=
  Πʳ i, [K i, O i]

theorem IQRestrictedProductCarrier_coe_mem
    {ι : Type*} {K : ι → Type*} {O : (i : ι) → Set (K i)}
    (x : IQRestrictedProductCarrier ι K O) :
    ∀ᶠ i in Filter.cofinite, x.1 i ∈ O i :=
  x.2

end LeanFormal.IUT.XiFPaper.Mzk1RestrictedProductReuseActual