/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1NormDeterminantToolsActual
import Mathlib.Tactic

/-! # P5-D / (C13): Galois invariance of the field norm -/

/-
| field | value |
|---|---|
| Status | green attempt: `N_{L/K}(σ α) = N_{L/K}(α)` for σ ∈ Gal(L/K), by reindexing the product formula |
| Reuse | `Mzk1NormDeterminantToolsActual.norm_galois_product`（product formula, green）; Mathlib `Fintype.prod_equiv` |
| GAP | (C18) restriction-of-scalars instance remains (GAP-NORM-TRANS) |
| 纪律 | no sorry/axiom; no new assumptions |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1GaloisNormInvarianceActual

open LeanFormal.IUT.XiFPaper.Mzk1NormDeterminantToolsActual

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]

/-- Right multiplication by `σ` is a permutation of the Galois group. -/
def galoisMulRightEquiv (σ : Gal(L/K)) : Gal(L/K) ≃ Gal(L/K) where
  toFun τ := τ * σ
  invFun τ := τ * σ⁻¹
  left_inv τ := by simp [mul_assoc]
  right_inv τ := by simp [mul_assoc]

/-- **(C13) invariance.**  The norm is invariant under Galois automorphisms:
`N_{L/K}(σ α) = N_{L/K}(α)`.  The proof uses the product formula
`norm_galois_product` and reindexes the product by right multiplication by `σ`. -/
theorem norm_galois_apply_eq (σ : Gal(L/K)) (α : L) :
    Algebra.norm K (σ α) = Algebra.norm K α := by
  apply FaithfulSMul.algebraMap_injective K L
  rw [norm_galois_product (K := K) (L := L) (σ α),
    norm_galois_product (K := K) (L := L) α]
  exact Fintype.prod_equiv (galoisMulRightEquiv σ)
    (fun τ : Gal(L/K) => τ (σ α)) (fun τ : Gal(L/K) => τ α)
    (by intro τ; rfl)

def galoisInvarianceRows : List (String × String) :=
  [ ("galoisMulRightEquiv", "right multiplication by sigma is a Galois-group permutation") ,
    ("norm_galois_apply_eq", "(C13) N(sigma alpha) = N(alpha) (PROVED)") ,
    ("GAP-NORM-TRANS", "(C18) restriction-of-scalars instance remains") ]

theorem galoisInvarianceRows_length : galoisInvarianceRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1GaloisNormInvarianceActual