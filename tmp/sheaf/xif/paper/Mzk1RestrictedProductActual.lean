/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-! # P7/#2: minimal restricted product structure (self-written; GAP toward IQ carrier) -/

/-
| field | value |
|---|---|
| Status | DEPRECATED-BY-REUSE: self-written minimal restricted product; Mathlib `RestrictedProduct` is the reuse target (`Mzk1RestrictedProductReuseActual.lean`) |
| Reuse | Mathlib `Filter.Eventually`; user instruction: try port first, else self-write minimal cluster |
| GAP | GAP-P7-IQ-LITERAL: paper IQ(S±; n, D^vdash) carrier still missing; this is only a generic restricted-product skeleton |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1RestrictedProductActual

/-- A restricted product: tuples that eventually lie in the prescribed local subsets.
For a finite index filter this is the ordinary product; for cofinite filters it is the
usual adelic/restricted product shape. -/
def RestrictedProduct
    (ι : Type*) (X : ι → Type*) (l : Filter ι) (U : (i : ι) → Set (X i)) : Type* :=
  {x : (i : ι) → X i // ∀ᶠ i in l, x i ∈ U i}

theorem RestrictedProduct.mem_iff
    {ι : Type*} {X : ι → Type*} {l : Filter ι} {U : (i : ι) → Set (X i)}
    (x : (i : ι) → X i) :
    x ∈ RestrictedProduct ι X l U ↔ ∀ᶠ i in l, x i ∈ U i :=
  Iff.rfl

/-- The unrestricted full product is the restricted product with `U = univ`. -/
theorem RestrictedProduct.univ_eq
    (ι : Type*) (X : ι → Type*) (l : Filter ι) :
    RestrictedProduct ι X l (fun _ => Set.univ) =
      {x : (i : ι) → X i // ∀ᶠ i in l, x i ∈ Set.univ} :=
  rfl

end LeanFormal.IUT.XiFPaper.Mzk1RestrictedProductActual