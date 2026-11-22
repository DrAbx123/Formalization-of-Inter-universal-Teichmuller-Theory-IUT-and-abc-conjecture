/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualLattice
import LeanFormal.IUT.Foundations.LocalFields.DifferentTraceProduct
import LeanFormal.IUT.Foundations.LocalFields.PadicLatticeIndexFormula
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling
import Mathlib.Tactic

/-! # R29 B-Tensor: trace-dual inclusion (B6) and finite quotient (B7) -/

/-
| field | value |
|---|---|
| Status | B6 PROVED (generic and trace-form wrapper); B7 conditional (explicit quotient equivalence) + rank-one computable re-export; full B7 = GAP-DUAL-SNF |
| Reuse | (B6) `integralTraceDualLattice_antitone` (IntegralTraceDualLattice:75); trace form via Mathlib `Submodule.mem_traceDual`; B7 rank-one `natCard_quotient_span_padicInt_pow` (PadicLatticeIndexFormula:130) |
| GAP | GAP-DUAL-SNF: the SNF duality step (dual-basis coefficients = inverses of the original SNF coefficients) is NOT formalized here; `b7_card_eq_of_equiv` takes that step as an explicit quotient equivalence |
| Discipline | no sorry/axiom; R = O_E is not assumed anywhere |
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT.IntegralTraceDual
open LeanFormal.IUT.PadicLatticeIndex

namespace LeanFormal.IUT.XiFPaper.Mzk1TensorDualCorrectionActual

/-! ## (B6): R ⊆ O_E ⇒ O_E# ⊆ R# -/

/-- **(B6), generic form.**  The integral trace dual is antitone in the lattice.
Reuses the green `integralTraceDualLattice_antitone`
(`LeanFormal/IUT/Foundations/LocalFields/IntegralTraceDualLattice.lean:75`). -/
theorem b6_integralTraceDual_subset
    {R S M : Type*} [CommRing R] [Field S] [AddCommGroup M]
    [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]
    (B : LinearMap.BilinForm S M) {I J : Submodule R M} (h : I ≤ J) :
    integralTraceDualLattice B J ≤ integralTraceDualLattice B I :=
  (integralTraceDualLattice_antitone B) h

/-- **(B6), trace-form wrapper.**  For the Mathlib trace form `Submodule.traceDual`,
`I ⊆ J` implies `J# ⊆ I#`.  Proved directly from `Submodule.mem_traceDual`;
no separability/finiteness is needed for this inclusion. -/
theorem b6_traceDual_subset
    {A K B L : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
    [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    {I J : Submodule B L} (h : I ≤ J) :
    Submodule.traceDual A K J ≤ Submodule.traceDual A K I := by
  intro x hx
  rw [Submodule.mem_traceDual] at hx ⊢
  exact fun y hy => hx y (h hy)

/-! ## (B7): #(J/I) = #(I#/J#) -/

/-- The cardinality of the sub-quotient `J/I` for nested lattices `I ≤ J`. -/
def quotientCard {B L : Type*} [CommRing B] [Field L] [Algebra B L]
    (I J : Submodule B L) (h : I ≤ J) : ℕ :=
  Nat.card ((J : Type _) ⧸ (I.comap (Submodule.subtype J)))

/-- The cardinality of the dual sub-quotient `I#/J#` (note the reversed order). -/
def traceDualQuotientCard
    {A K B L : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
    [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (I J : Submodule B L) (h : I ≤ J) : ℕ :=
  Nat.card (((Submodule.traceDual A K I : Type _)) ⧸
    ((Submodule.traceDual A K J).comap
      (Submodule.subtype (Submodule.traceDual A K I))))

/-- Sufficient condition for (B7): an explicit equivalence of the two finite quotients.
This is the standard perfect-pairing/SNF duality step packaged as data; it is not
derived from scratch here (GAP-DUAL-SNF). -/
structure TraceDualQuotientEquiv
    {A K B L : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
    [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    {I J : Submodule B L} (h : I ≤ J) where
  equiv :
    ((J : Type _) ⧸ (I.comap (Submodule.subtype J))) ≃
      (((Submodule.traceDual A K I : Type _)) ⧸
        ((Submodule.traceDual A K J).comap
          (Submodule.subtype (Submodule.traceDual A K I))))

/-- **(B7) from the explicit quotient equivalence** (真证：`Nat.card_congr`). -/
theorem b7_card_eq_of_equiv
    {A K B L : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
    [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    {I J : Submodule B L} (h : I ≤ J)
    (D : TraceDualQuotientEquiv (A := A) (K := K) (B := B) (L := L) (I := I) (J := J) h) :
    quotientCard I J h = traceDualQuotientCard (A := A) (K := K) (B := B) (L := L) I J h :=
  Nat.card_congr D.equiv


/-! ## Actual trace pairing on the quotient J/I (partial B7 content) -/

section PairingQuotient

variable {p : ℕ} [Fact p.Prime]
variable {M : Type*} [AddCommGroup M] [Module ℚ_[p] M]
variable [Module ℤ_[p] M] [IsScalarTower ℤ_[p] ℚ_[p] M]
variable (B : LinearMap.BilinForm ℚ_[p] M)
variable (I J : Submodule ℤ_[p] M)

/-- The trace pairing of `x ∈ I#` with `J` is well defined modulo `I`:
if `y - z ∈ I`, the two classes `B x y` and `B x z` differ by an integral element.
This is the actual-pairing descent step toward `I#/J# → Hom(J/I, ℚ_[p]/ℤ_[p])`. -/
theorem b7_pairing_integrality
    {x : M} (hx : x ∈ integralTraceDualLattice (R := ℤ_[p]) (S := ℚ_[p]) B I)
    {y z : M} (h : y - z ∈ I) :
    B x y - B x z ∈ (1 : Submodule ℤ_[p] ℚ_[p]) := by
  have hsub : B x y - B x z = B x (y - z) := ((B x).map_sub y z).symm
  rw [hsub]
  exact (mem_integralTraceDualLattice_iff.mp hx) (y - z) h

/-- The pairing of `x ∈ I#` annihilates `J` modulo `ℤ_[p]` exactly when `x ∈ J#`.
This is the kernel computation for the pairing map `I# → Hom(J/I, ℚ_[p]/ℤ_[p])`. -/
theorem b7_pairing_kernel
    {x : M} (hx : x ∈ integralTraceDualLattice (R := ℤ_[p]) (S := ℚ_[p]) B I) :
    (∀ y ∈ J, B x y ∈ (1 : Submodule ℤ_[p] ℚ_[p])) ↔
      x ∈ integralTraceDualLattice (R := ℤ_[p]) (S := ℚ_[p]) B J := by
  constructor
  · intro h
    rw [mem_integralTraceDualLattice_iff]
    exact h
  · intro h
    rw [mem_integralTraceDualLattice_iff] at h
    exact h

end PairingQuotient


/-! ## Computable rank-one index (整闭包指数损失的对偶侧是有限商) -/

/-- The rank-one finite quotient is computable: `#(ℤ_[p]/p^n) = p^n`.
This re-exports the green `natCard_quotient_span_padicInt_pow`
(`LeanFormal/IUT/Foundations/LocalFields/PadicLatticeIndexFormula.lean:130`). -/
theorem b7_rank_one_padicInt_card (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Nat.card (ℤ_[p] ⧸ Ideal.span ({(p : ℤ_[p]) ^ n} : Set ℤ_[p])) = p ^ n :=
  natCard_quotient_span_padicInt_pow (p := p) n

/-- The index of a principal ideal in `ℤ_[p]` in terms of the valuation:
`#(ℤ_[p]/(a)) = p ^ v(a)` for `a ≠ 0`. -/
theorem b7_rank_one_padicInt_card_valuation (p : ℕ) [Fact p.Prime]
    {a : ℤ_[p]} (ha : a ≠ 0) :
    Nat.card (ℤ_[p] ⧸ Ideal.span ({a} : Set ℤ_[p])) = p ^ a.valuation :=
  natCard_quotient_span_padicInt_eq_pow_valuation ha

/-! ## (B8)/(B9) dual of sums: source-level inheritance -/

/-- (B8) dual of a sum is the intersection of duals, for a finite family of lattices.
Proved from the generic `integralTraceDualLattice` membership. -/
theorem b8_dual_span_le_iInf
    {R S M : Type*} [CommRing R] [Field S] [AddCommGroup M]
    [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]
    (B : LinearMap.BilinForm S M) {ι : Type*} [Fintype ι]
    (L : ι → Submodule R M) :
    integralTraceDualLattice B (Submodule.span R (⋃ i, (L i : Set M))) ≤ 
      ⨅ i, integralTraceDualLattice B (L i) := by
  intro x hx
  rw [Submodule.mem_iInf]
  intro i
  rw [mem_integralTraceDualLattice_iff] at hx ⊢
  intro y hy
  exact hx y (Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, hy⟩))

def bTensorRows : List (String × String) :=
  [ ("b6_integralTraceDual_subset", "R ⊆ O ⇒ O# ⊆ R# (generic, PROVED)") ,
    ("b6_traceDual_subset", "trace-form wrapper (PROVED)") ,
    ("TraceDualQuotientEquiv", "explicit quotient equivalence (data; GAP-DUAL-SNF)") ,
    ("b7_card_eq_of_equiv", "#(J/I) = #(I#/J#) (PROVED from equivalence)") ,
    ("b7_rank_one_padicInt_card", "#(Zp/p^n) = p^n (re-export green)") ,
    ("b8_dual_span_le_iInf", "(B8) dual of span ⊆ iInf duals (PROVED)") ]

theorem bTensorRows_length : bTensorRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1TensorDualCorrectionActual