import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Index of a full-rank sublattice of a finite free `ℤ_[p]`-module

For a finite free module `M` over a principal ideal domain `R` and a submodule `N` of
full rank, Mathlib's Smith normal form gives bases `bM`, `bN` and coefficients `a` with
`(bN i : M) = a i • bM i`. This file derives from such a witness the quotient-cardinality
formula

`Nat.card (M ⧸ N) = ∏ i, Nat.card (R ⧸ Ideal.span {a i})`.

Specialising to `R = ℤ_[p]` and writing each coefficient as `a i = u i * p ^ k i` with
`u i` a unit yields `Nat.card (M ⧸ N) = p ^ ∑ i, k i`. The unit decomposition is
Mathlib's `PadicInt.unitCoeff_spec`; the quotient `ℤ_[p] ⧸ span {p ^ n}` is identified
with `ZMod (p ^ n)` through `PadicInt.toZModPow`.

No Smith normal form is reconstructed here: the explicit-witness theorem accepts the
diagonal data, and the rank-equality theorem invokes Mathlib's
`Submodule.smithNormalFormOfRankEq` / `Submodule.exists_smith_normal_form_of_rank_eq`.
-/

namespace LeanFormal.IUT.PadicLatticeIndex

noncomputable section

open Module

/-! ## Quotient cardinality from an explicit Smith normal form -/

/-- If the inclusion `N → M` is diagonal in the bases `bN` and `bM` with diagonal
entries `a`, then the cardinality of `M ⧸ N` is the product of the cardinalities of
the principal quotients `R ⧸ (a i)`. -/
theorem natCard_quotient_eq_prod_span_of_smithNormalForm
    {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    {N : Submodule R M} {bM : Basis ι R M} {bN : Basis ι R N} {a : ι → R}
    (hSNF : ∀ i, (bN i : M) = a i • bM i) :
    Nat.card (M ⧸ N) = ∏ i, Nat.card (R ⧸ Ideal.span ({a i} : Set R)) := by
  classical
  have hmem : ∀ x : M, x ∈ N ↔ ∀ i, a i ∣ bM.repr x i := by
    intro x
    rw [bN.mem_submodule_iff']
    constructor
    · rintro ⟨c, rfl⟩ i
      have hcoord : bM.repr (∑ j, c j • (bN j : M)) i = c i * a i := by
        simp only [← mul_smul, hSNF, bM.repr_sum_self]
      exact ⟨c i, by rw [hcoord, mul_comm]⟩
    · rintro hdvd
      choose c hc using hdvd
      refine ⟨c, ?_⟩
      calc
        x = ∑ i, bM.repr x i • bM i := (bM.sum_repr x).symm
        _ = ∑ i, (a i * c i) • bM i := by simp_rw [hc]
        _ = ∑ i, c i • (bN i : M) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hSNF i, smul_smul, mul_comm (a i) (c i)]
  let N' : Submodule R (ι → R) := Submodule.pi Set.univ fun i => Ideal.span ({a i} : Set R)
  have hmap : Submodule.map (bM.equivFun : M →ₗ[R] ι → R) N = N' := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [N', Submodule.mem_pi, Set.mem_univ, forall_true_left]
      intro i
      change bM.repr y i ∈ Ideal.span ({a i} : Set R)
      exact Ideal.mem_span_singleton.mpr ((hmem y).mp hy i)
    · intro hx
      simp only [N', Submodule.mem_pi, Set.mem_univ, forall_true_left] at hx
      refine ⟨∑ i, x i • bM i, (hmem _).mpr ?_, ?_⟩
      · intro i
        rw [bM.repr_sum_self]
        exact Ideal.mem_span_singleton.mp (hx i)
      · change bM.repr (∑ i, x i • bM i) = x
        rw [bM.repr_sum_self]
  calc
    Nat.card (M ⧸ N) = Nat.card ((ι → R) ⧸ N') :=
      Nat.card_congr (Submodule.Quotient.equiv N N' bM.equivFun hmap).toEquiv
    _ = Nat.card (∀ i, R ⧸ Ideal.span ({a i} : Set R)) :=
      Nat.card_congr (Submodule.quotientPi (fun i => Ideal.span ({a i} : Set R))).toEquiv
    _ = ∏ i, Nat.card (R ⧸ Ideal.span ({a i} : Set R)) := Nat.card_pi

/-- A nonzero diagonal coefficient in a Smith normal form over a nontrivial ring. -/
theorem ne_zero_of_smithNormalForm
    {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Nontrivial R]
    {N : Submodule R M} {bM : Basis ι R M} {bN : Basis ι R N} {a : ι → R}
    (hSNF : ∀ i, (bN i : M) = a i • bM i) (i : ι) : a i ≠ 0 := by
  intro ha
  have hzero : (bN i : M) = 0 := by rw [hSNF i, ha, zero_smul]
  exact bN.ne_zero i (Subtype.coe_injective (by simpa using hzero))

/-- The Smith normal form produced by Mathlib, together with the quotient cardinality
formula for the coefficients appearing in that witness. -/
theorem exists_smithNormalForm_and_natCard_quotient_eq_prod_span
    {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsDomain R] [IsPrincipalIdealRing R] [Fintype ι]
    (N : Submodule R M) (b : Basis ι R M)
    (h : Module.finrank R N = Module.finrank R M) :
    ∃ (bM : Basis ι R M) (a : ι → R) (bN : Basis ι R N),
      (∀ i, (bN i : M) = a i • bM i) ∧
        Nat.card (M ⧸ N) = ∏ i, Nat.card (R ⧸ Ideal.span ({a i} : Set R)) := by
  obtain ⟨bM, a, bN, hSNF⟩ := Submodule.exists_smith_normal_form_of_rank_eq b h
  exact ⟨bM, a, bN, hSNF, natCard_quotient_eq_prod_span_of_smithNormalForm hSNF⟩

/-- Cardinality formula in terms of Mathlib's chosen Smith normal form coefficients. -/
theorem natCard_quotient_eq_prod_span_smithNormalFormCoeffs
    {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsDomain R] [IsPrincipalIdealRing R] [Fintype ι]
    (N : Submodule R M) (b : Basis ι R M)
    (h : Module.finrank R N = Module.finrank R M) :
    Nat.card (M ⧸ N) =
      ∏ i, Nat.card (R ⧸ Ideal.span ({Submodule.smithNormalFormCoeffs b h i} : Set R)) := by
  rw [Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv, Nat.card_pi]

/-! ## Quotients of `ℤ_[p]` by powers of `p` -/

section PadicIntegers

variable {p : ℕ} [Fact p.Prime]

/-- The quotient of `ℤ_[p]` by the ideal generated by `p ^ n` is `ZMod (p ^ n)`. -/
def padicIntQuotientEquivZMod (n : ℕ) :
    (ℤ_[p] ⧸ Ideal.span ({(p : ℤ_[p]) ^ n} : Set ℤ_[p])) ≃+* ZMod (p ^ n) :=
  (Ideal.quotEquivOfEq (PadicInt.ker_toZModPow n).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) n)))

/-- The quotient of `ℤ_[p]` by `p ^ n` has cardinality `p ^ n`. -/
theorem natCard_quotient_span_padicInt_pow (n : ℕ) :
    Nat.card (ℤ_[p] ⧸ Ideal.span ({(p : ℤ_[p]) ^ n} : Set ℤ_[p])) = p ^ n := by
  rw [Nat.card_congr (padicIntQuotientEquivZMod (p := p) n).toEquiv, Nat.card_zmod]

/-- A principal quotient of `ℤ_[p]` by a unit multiple of `p ^ k` has cardinality
`p ^ k`. -/
theorem natCard_quotient_span_padicInt_eq_pow_of_unit_mul_pow
    {a : ℤ_[p]} {u : ℤ_[p]ˣ} {k : ℕ}
    (ha : a = (u : ℤ_[p]) * (p : ℤ_[p]) ^ k) :
    Nat.card (ℤ_[p] ⧸ Ideal.span ({a} : Set ℤ_[p])) = p ^ k := by
  rw [ha, Ideal.span_singleton_mul_left_unit (Units.isUnit u) ((p : ℤ_[p]) ^ k),
    natCard_quotient_span_padicInt_pow]

/-- A nonzero principal quotient of `ℤ_[p]` has cardinality `p ^ valuation`. -/
theorem natCard_quotient_span_padicInt_eq_pow_valuation
    {a : ℤ_[p]} (ha : a ≠ 0) :
    Nat.card (ℤ_[p] ⧸ Ideal.span ({a} : Set ℤ_[p])) = p ^ a.valuation :=
  natCard_quotient_span_padicInt_eq_pow_of_unit_mul_pow
    (u := PadicInt.unitCoeff ha) (k := a.valuation) (PadicInt.unitCoeff_spec ha)

/-! ## The lattice index formula -/

/-- The literal product formula for a `ℤ_[p]`-lattice with an explicit Smith normal
form. -/
theorem natCard_quotient_eq_prod_span_padicInt_of_smithNormalForm
    {ι M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Fintype ι]
    {N : Submodule ℤ_[p] M} {bM : Basis ι ℤ_[p] M} {bN : Basis ι ℤ_[p] N}
    {a : ι → ℤ_[p]}
    (hSNF : ∀ i, (bN i : M) = a i • bM i) :
    Nat.card (M ⧸ N) =
      ∏ i, Nat.card (ℤ_[p] ⧸ Ideal.span ({a i} : Set ℤ_[p])) :=
  natCard_quotient_eq_prod_span_of_smithNormalForm hSNF

/-- The product formula for a `ℤ_[p]`-lattice in terms of valuations. -/
theorem natCard_quotient_eq_prod_pow_valuation_of_smithNormalForm
    {ι M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Fintype ι]
    {N : Submodule ℤ_[p] M} {bM : Basis ι ℤ_[p] M} {bN : Basis ι ℤ_[p] N}
    {a : ι → ℤ_[p]}
    (hSNF : ∀ i, (bN i : M) = a i • bM i) :
    Nat.card (M ⧸ N) = ∏ i, p ^ (a i).valuation := by
  rw [natCard_quotient_eq_prod_span_of_smithNormalForm hSNF]
  exact Finset.prod_congr rfl fun i _ =>
    natCard_quotient_span_padicInt_eq_pow_valuation (ne_zero_of_smithNormalForm hSNF i)

/-- The `p`-power lattice index formula: if every Smith normal form coefficient is a
unit times `p ^ k i`, then the quotient has cardinality `p ^ ∑ i, k i`. -/
theorem natCard_quotient_eq_pow_sum_of_unit_mul_pow
    {ι M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Fintype ι]
    {N : Submodule ℤ_[p] M} {bM : Basis ι ℤ_[p] M} {bN : Basis ι ℤ_[p] N}
    {a : ι → ℤ_[p]} {u : ι → ℤ_[p]ˣ} {k : ι → ℕ}
    (hSNF : ∀ i, (bN i : M) = a i • bM i)
    (ha : ∀ i, a i = (u i : ℤ_[p]) * (p : ℤ_[p]) ^ k i) :
    Nat.card (M ⧸ N) = p ^ ∑ i, k i := by
  rw [natCard_quotient_eq_prod_span_of_smithNormalForm hSNF]
  have hprod : (∏ i, Nat.card (ℤ_[p] ⧸ Ideal.span ({a i} : Set ℤ_[p]))) =
      ∏ i, p ^ k i :=
    Finset.prod_congr rfl fun i _ =>
      natCard_quotient_span_padicInt_eq_pow_of_unit_mul_pow (ha i)
  rw [hprod]
  simpa using Finset.prod_pow_eq_pow_sum (Finset.univ : Finset ι) k p

/-- The product formula for Mathlib's chosen Smith normal form coefficients over
`ℤ_[p]`, in terms of valuations. -/
theorem natCard_quotient_eq_prod_pow_valuation_of_rankEq
    {ι M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Fintype ι]
    (N : Submodule ℤ_[p] M) (b : Basis ι ℤ_[p] M)
    (h : Module.finrank ℤ_[p] N = Module.finrank ℤ_[p] M) :
    Nat.card (M ⧸ N) =
      ∏ i, p ^ (Submodule.smithNormalFormCoeffs b h i).valuation := by
  rw [natCard_quotient_eq_prod_span_smithNormalFormCoeffs N b h]
  exact Finset.prod_congr rfl fun i _ =>
    natCard_quotient_span_padicInt_eq_pow_valuation
      (Submodule.smithNormalFormCoeffs_ne_zero b h i)

/-- The `p`-power index formula for Mathlib's chosen Smith normal form coefficients. -/
theorem natCard_quotient_eq_pow_sum_of_rankEq_unit_mul_pow
    {ι M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Fintype ι]
    (N : Submodule ℤ_[p] M) (b : Basis ι ℤ_[p] M)
    (h : Module.finrank ℤ_[p] N = Module.finrank ℤ_[p] M)
    (u : ι → ℤ_[p]ˣ) (k : ι → ℕ)
    (hunit : ∀ i,
      Submodule.smithNormalFormCoeffs b h i = (u i : ℤ_[p]) * (p : ℤ_[p]) ^ k i) :
    Nat.card (M ⧸ N) = p ^ ∑ i, k i := by
  rw [natCard_quotient_eq_prod_span_smithNormalFormCoeffs N b h]
  have hprod : (∏ i, Nat.card (ℤ_[p] ⧸
      Ideal.span ({Submodule.smithNormalFormCoeffs b h i} : Set ℤ_[p]))) = ∏ i, p ^ k i :=
    Finset.prod_congr rfl fun i _ =>
      natCard_quotient_span_padicInt_eq_pow_of_unit_mul_pow (hunit i)
  rw [hprod]
  simpa using Finset.prod_pow_eq_pow_sum (Finset.univ : Finset ι) k p

/-- The product formula for a finite free `ℤ_[p]`-module, with no explicit basis. -/
theorem natCard_quotient_eq_prod_pow_valuation_of_finiteFree
    {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M]
    {N : Submodule ℤ_[p] M}
    (h : Module.finrank ℤ_[p] N = Module.finrank ℤ_[p] M) :
    Nat.card (M ⧸ N) = ∏ i,
      p ^ (Submodule.smithNormalFormCoeffs (Module.Free.chooseBasis ℤ_[p] M) h i).valuation :=
  natCard_quotient_eq_prod_pow_valuation_of_rankEq N (Module.Free.chooseBasis ℤ_[p] M) h

/-- The `p`-power index formula for a finite free `ℤ_[p]`-module, with no explicit
basis. -/
theorem natCard_quotient_eq_pow_sum_of_finiteFree_unit_mul_pow
    {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M]
    {N : Submodule ℤ_[p] M}
    (h : Module.finrank ℤ_[p] N = Module.finrank ℤ_[p] M)
    (u : Module.Free.ChooseBasisIndex ℤ_[p] M → ℤ_[p]ˣ)
    (k : Module.Free.ChooseBasisIndex ℤ_[p] M → ℕ)
    (hunit : ∀ i, Submodule.smithNormalFormCoeffs (Module.Free.chooseBasis ℤ_[p] M) h i =
      (u i : ℤ_[p]) * (p : ℤ_[p]) ^ k i) :
    Nat.card (M ⧸ N) = p ^ ∑ i, k i :=
  natCard_quotient_eq_pow_sum_of_rankEq_unit_mul_pow N (Module.Free.chooseBasis ℤ_[p] M) h
    u k hunit

end PadicIntegers

end

end LeanFormal.IUT.PadicLatticeIndex
