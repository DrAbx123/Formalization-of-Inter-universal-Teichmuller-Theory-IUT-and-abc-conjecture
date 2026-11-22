import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Multilinear.Basic
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicIntegerTensorLattice
import LeanFormal.IUT.Foundations.LocalFields.PadicLatticeIndexFormula

/-!
# Tensor-index arithmetic for finite families of full-rank lattices

This file proves the relative-index formula for tensor products of free
lattices over `Zp`, together with its instantiation to the arithmetic
tuple integral-log and valuation-integer lattices.
-/

namespace LeanFormal.IUT.TensorIndexArithmetic

open Submodule
open Module
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.FinitePadicIntegralLattice
open scoped LeanFormal.IUT.FinitePadicIntegralLattice

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The cardinality of `R ⧸ (a)` is multiplicative in `a` in a domain:
`#(R/(ab)) = #(R/(a)) * #(R/(b))` for nonzero `a`, `b`.
This is the exact-sequence computation
`0 -> (a)/(ab) -> R/(ab) -> R/(a) -> 0`
together with `(a)/(ab) ≃ R/(b)`. -/
lemma natCard_quotient_span_mul (a b : R) (ha : a ≠ 0) (_hb : b ≠ 0) :
    Nat.card (R ⧸ Ideal.span ({a * b} : Set R)) =
      Nat.card (R ⧸ Ideal.span ({a} : Set R)) *
        Nat.card (R ⧸ Ideal.span ({b} : Set R)) := by
  classical
  let S : Submodule R R := Ideal.span ({a} : Set R)
  let T : Submodule R R := Ideal.span ({a * b} : Set R)
  have hST : T ≤ S := by
    change Ideal.span ({a * b} : Set R) ≤ Ideal.span ({a} : Set R)
    rw [Ideal.span_le]
    rintro x rfl
    exact Ideal.mul_mem_right b (Ideal.span ({a} : Set R))
      (Ideal.mem_span_singleton_self a)
  have hcard := Submodule.card_quotient_mul_card_quotient S T hST
  let g : R →ₗ[R] S.map T.mkQ :=
    (T.mkQ.comp (LinearMap.mulLeft R a)).codRestrict (S.map T.mkQ) (by
      intro x
      exact Submodule.mem_map.mpr
        ⟨a * x, Ideal.mul_mem_right x (Ideal.span ({a} : Set R))
          (Ideal.mem_span_singleton_self a), rfl⟩)
  let f : (R ⧸ Ideal.span ({b} : Set R)) →ₗ[R] S.map T.mkQ :=
    (Ideal.span ({b} : Set R)).liftQ g (by
      intro x hx
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      change Submodule.Quotient.mk (a * x) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      change a * x ∈ Ideal.span ({a * b} : Set R)
      rw [Ideal.mem_span_singleton] at hx ⊢
      rcases hx with ⟨c, rfl⟩
      exact ⟨c, by ring⟩)
  have hf_inj : Function.Injective f := by
    intro x y hxy
    induction x using Quotient.inductionOn with
    | _ x =>
      induction y using Quotient.inductionOn with
      | _ y =>
        have hxy' : (Submodule.Quotient.mk (p := Ideal.span ({a * b} : Set R)) (a * x) :
            R ⧸ Ideal.span ({a * b} : Set R)) =
            Submodule.Quotient.mk (p := Ideal.span ({a * b} : Set R)) (a * y) := by
          have hval := congrArg Subtype.val hxy
          change T.mkQ (a * x) = T.mkQ (a * y) at hval
          change Submodule.Quotient.mk (a * x) = Submodule.Quotient.mk (a * y) at hval
          exact hval
        rw [Submodule.Quotient.eq] at hxy'
        change (Submodule.Quotient.mk (p := Ideal.span ({b} : Set R)) x :
            R ⧸ Ideal.span ({b} : Set R)) =
          Submodule.Quotient.mk (p := Ideal.span ({b} : Set R)) y
        rw [Submodule.Quotient.eq]
        change x - y ∈ Ideal.span ({b} : Set R)
        rw [Ideal.mem_span_singleton] at hxy' ⊢
        rcases hxy' with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        have h : a * (x - y) = a * (b * c) := by
          rw [mul_sub, hc, mul_assoc]
        exact mul_left_cancel₀ ha h
  have hf_surj : Function.Surjective f := by
    rintro ⟨z, hz⟩
    rcases hz with ⟨w, hw, rfl⟩
    change w ∈ Ideal.span ({a} : Set R) at hw
    rw [Ideal.mem_span_singleton] at hw
    rcases hw with ⟨x, rfl⟩
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    apply Subtype.ext
    simp only [f, g, Submodule.liftQ_apply, LinearMap.codRestrict_apply]
    rfl
  let e : (R ⧸ Ideal.span ({b} : Set R)) ≃ₗ[R] S.map T.mkQ :=
    LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have h := hcard
  rw [← Nat.card_congr e.toEquiv, Nat.mul_comm] at h
  simpa [S, T] using h.symm

/-- Multiplicativity of the principal-quotient cardinality over a finite product of
nonzero elements of a domain. -/
lemma natCard_quotient_span_finset_prod {ι : Type*}
    (s : Finset ι) (a : ι → R) (ha : ∀ i ∈ s, a i ≠ 0) :
    Nat.card (R ⧸ Ideal.span ({∏ i ∈ s, a i} : Set R)) =
      ∏ i ∈ s, Nat.card (R ⧸ Ideal.span ({a i} : Set R)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Ideal.span_singleton_one]
      exact Nat.card_eq_one_iff_unique.mpr
        ⟨inferInstance, ⟨(0 : R ⧸ (⊤ : Ideal R))⟩⟩
  | insert x s hx ih =>
      rw [Finset.prod_insert hx, Finset.prod_insert hx,
        natCard_quotient_span_mul _ _
          (ha x (Finset.mem_insert_self x s))
          (Finset.prod_ne_zero_iff.mpr fun i hi =>
            ha i (Finset.mem_insert_of_mem hi))]
      rw [ih fun i hi => ha i (Finset.mem_insert_of_mem hi)]

/-- Multiplicativity of the principal-quotient cardinality over a finite type. -/
lemma natCard_quotient_span_fintype_prod {ι : Type*} [Fintype ι]
    (a : ι → R) (ha : ∀ i, a i ≠ 0) :
    Nat.card (R ⧸ Ideal.span ({∏ i, a i} : Set R)) =
      ∏ i, Nat.card (R ⧸ Ideal.span ({a i} : Set R)) := by
  simpa using natCard_quotient_span_finset_prod (Finset.univ) a (fun i _ => ha i)

/-- Reindex a product over a dependent function type: the product of all coordinate
contributions is the product over coordinates of the local product raised to the
number of tuples differing only away from that coordinate. -/
lemma prod_pi_prod_eq_prod_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    [productIndexFintype : Fintype (Π i, κ i)]
    (c : (i : ι) → κ i → ℕ) :
    (∏ k : Π i, κ i, ∏ i, c i (k i)) =
      ∏ i, (∏ k, c i k) ^ (∏ j ∈ Finset.univ.erase i, Fintype.card (κ j)) := by
  classical
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  calc
    (∏ k : Π j, κ j, c i (k i))
        = ∏ p : κ i × (Π j : {j // j ≠ i}, κ j), c i p.1 := by
          simpa only [Equiv.piSplitAt_apply] using
            (Equiv.prod_comp (Equiv.piSplitAt i κ) fun p => c i p.1)
    _ = ∏ a : κ i, ∏ _b : (Π j : {j // j ≠ i}, κ j), c i a :=
          Fintype.prod_prod_type fun p : κ i × (Π j : {j // j ≠ i}, κ j) => c i p.1
    _ = (∏ a : κ i, c i a) ^ (∏ j ∈ Finset.univ.erase i, Fintype.card (κ j)) := by
          rw [← Finset.prod_pow]
          refine Finset.prod_congr rfl fun a _ => ?_
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_pi]
          exact congrArg (fun n => (c i a) ^ n)
            (Finset.prod_subtype (p := fun x => x ≠ i) (Finset.univ.erase i)
              (fun x => by simp) (fun j => Fintype.card (κ j))).symm

/-! ## Local Smith normal form of the integer lattice inside the log shell -/

variable {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [Fintype ι]
variable (A : ι → Type*)
variable [∀ i, NormedField (A i)]
variable [∀ i, NormedAlgebra ℚ_[p] (A i)]
variable [∀ i, FiniteDimensional ℚ_[p] (A i)]
variable [∀ i, CharZero (A i)]
variable [∀ i, CompleteSpace (A i)]
variable [∀ i, IsUltrametricDist (A i)]
variable [∀ i, ProperSpace (A i)]

/-- The local integral logarithmic shell lattice. -/
abbrev LocalIntegralLogShell (i : ι) : Submodule ℤ_[p] (A i) :=
  integralLogShellLattice (K := A i) (p := p)

/-- The local valuation-integer lattice. -/
abbrev LocalIntegerLattice (i : ι) : Submodule ℤ_[p] (A i) :=
  valuationIntegerLattice (K := A i) (p := p)

/-- The valuation-integer lattice cut out inside the integral log shell.  Its quotient
cardinality is the local lattice index `[I_i : O_i]`. -/
abbrev LocalIntegerInLogShell (i : ι) :
    Submodule ℤ_[p] (LocalIntegralLogShell (p := p) A i) :=
  (LocalIntegerLattice (p := p) A i).comap
    (LocalIntegralLogShell (p := p) A i).subtype

theorem localIntegerLattice_le_logShell (i : ι) :
    LocalIntegerLattice (p := p) A i ≤ LocalIntegralLogShell (p := p) A i :=
  valuationIntegerLattice_le_integralLogShellLattice (K := A i) (p := p)

theorem finrank_localIntegerLattice (i : ι) :
    Module.finrank ℤ_[p] (LocalIntegerLattice (p := p) A i) =
      Module.finrank ℚ_[p] (A i) :=
  finrank_of_full_integral_submodule (LocalIntegerLattice (p := p) A i)
    (span_padic_valuationIntegerLattice_eq_top (p := p) (K := A i))

theorem finrank_localIntegerInLogShell (i : ι) :
    Module.finrank ℤ_[p] (LocalIntegerInLogShell (p := p) A i) =
      Module.finrank ℤ_[p] (LocalIntegralLogShell (p := p) A i) := by
  have h1 : Module.finrank ℤ_[p] (LocalIntegerInLogShell (p := p) A i) =
      Module.finrank ℤ_[p] (LocalIntegerLattice (p := p) A i) :=
    (Submodule.comapSubtypeEquivOfLe
      (localIntegerLattice_le_logShell (p := p) A i)).finrank_eq
  have h2 : Module.finrank ℤ_[p] (LocalIntegralLogShell (p := p) A i) =
      Module.finrank ℚ_[p] (A i) :=
    finrank_integralLogShellLattice (K := A i) (p := p)
  rw [h1, finrank_localIntegerLattice (p := p) A i, h2]

/-- The common Smith index of the local pair `O_i ≤ I_i`. -/
abbrev LocalSmithIndex (i : ι) : Type _ :=
  Module.Free.ChooseBasisIndex ℤ_[p] (LocalIntegralLogShell (p := p) A i)

instance localSmithIndexFintype (i : ι) : Fintype (LocalSmithIndex (p := p) A i) :=
  inferInstance

/-- The Smith basis of the local log-shell lattice. -/
noncomputable def localSmithBasisI (i : ι) :
    Basis (LocalSmithIndex (p := p) A i) ℤ_[p]
      (LocalIntegralLogShell (p := p) A i) :=
  Submodule.smithNormalFormTopBasis
    (Module.Free.chooseBasis ℤ_[p] (LocalIntegralLogShell (p := p) A i))
    (finrank_localIntegerInLogShell (p := p) A i)

/-- The diagonal Smith coefficients of the local inclusion `O_i ≤ I_i`. -/
noncomputable def localSmithCoeff (i : ι) :
    LocalSmithIndex (p := p) A i → ℤ_[p] :=
  Submodule.smithNormalFormCoeffs
    (Module.Free.chooseBasis ℤ_[p] (LocalIntegralLogShell (p := p) A i))
    (finrank_localIntegerInLogShell (p := p) A i)

/-- The Smith basis of the local integer sublattice, viewed inside the log shell. -/
noncomputable def localSmithBasisN (i : ι) :
    Basis (LocalSmithIndex (p := p) A i) ℤ_[p]
      (LocalIntegerInLogShell (p := p) A i) :=
  Submodule.smithNormalFormBotBasis
    (Module.Free.chooseBasis ℤ_[p] (LocalIntegralLogShell (p := p) A i))
    (finrank_localIntegerInLogShell (p := p) A i)

theorem localSmithBasisN_diagonal (i : ι) (k : LocalSmithIndex (p := p) A i) :
    (localSmithBasisN (p := p) A i k : LocalIntegralLogShell (p := p) A i) =
      localSmithCoeff (p := p) A i k • localSmithBasisI (p := p) A i k :=
  Submodule.smithNormalFormBotBasis_def
    (Module.Free.chooseBasis ℤ_[p] (LocalIntegralLogShell (p := p) A i))
    (finrank_localIntegerInLogShell (p := p) A i) k

theorem localSmithCoeff_ne_zero (i : ι) (k : LocalSmithIndex (p := p) A i) :
    localSmithCoeff (p := p) A i k ≠ 0 :=
  Submodule.smithNormalFormCoeffs_ne_zero
    (Module.Free.chooseBasis ℤ_[p] (LocalIntegralLogShell (p := p) A i))
    (finrank_localIntegerInLogShell (p := p) A i) k

/-- The Smith basis of the local integer lattice itself. -/
noncomputable def localSmithBasisO (i : ι) :
    Basis (LocalSmithIndex (p := p) A i) ℤ_[p]
      (LocalIntegerLattice (p := p) A i) :=
  (localSmithBasisN (p := p) A i).map
    (Submodule.comapSubtypeEquivOfLe
      (localIntegerLattice_le_logShell (p := p) A i))

theorem localSmithBasisO_apply (i : ι) (k : LocalSmithIndex (p := p) A i) :
    (localSmithBasisO (p := p) A i k : A i) =
      localSmithCoeff (p := p) A i k • (localSmithBasisI (p := p) A i k : A i) := by
  have h := congrArg (fun x : LocalIntegralLogShell (p := p) A i => (x : A i))
    (localSmithBasisN_diagonal (p := p) A i k)
  simpa [localSmithBasisO, Basis.map_apply, Submodule.comapSubtypeEquivOfLe_apply_coe]
    using h

/-- The local index formula: the quotient `I_i / O_i` has cardinality the product of
the principal quotients of the Smith coefficients. -/
theorem natCard_localLogShell_quotient_localInteger_eq_prod_span (i : ι) :
    Nat.card (LocalIntegralLogShell (p := p) A i ⧸
      LocalIntegerInLogShell (p := p) A i) =
      ∏ k : LocalSmithIndex (p := p) A i,
        Nat.card (ℤ_[p] ⧸
          Ideal.span ({localSmithCoeff (p := p) A i k} : Set ℤ_[p])) :=
  LeanFormal.IUT.PadicLatticeIndex.natCard_quotient_eq_prod_span_of_smithNormalForm
    (fun k => localSmithBasisN_diagonal (p := p) A i k)

/-! ## The tensor Smith basis and the tensor index formula -/

/-- The product index of the tensor Smith basis. -/
abbrev TensorSmithIndex : Type _ :=
  (i : ι) → LocalSmithIndex (p := p) A i

instance tensorSmithIndexFintype : Fintype (TensorSmithIndex (p := p) A) := by
  classical
  dsimp [TensorSmithIndex]
  infer_instance

/-- The tensor Smith basis of the integral log-shell lattice. -/
noncomputable def tensorLogShellBasis :
    Basis (TensorSmithIndex (p := p) A) ℤ_[p]
      (tensorLogShellLattice (p := p) A) :=
  (Basis.piTensorProduct fun i => localSmithBasisI (p := p) A i).map
    (integralLogTensorEquivLattice (p := p) A)

/-- The tensor Smith basis of the valuation-integer lattice. -/
noncomputable def tensorIntegerBasisO :
    Basis (TensorSmithIndex (p := p) A) ℤ_[p]
      (tensorIntegerLattice (p := p) A) :=
  (Basis.piTensorProduct fun i => localSmithBasisO (p := p) A i).map
    (integerTensorEquivLattice (p := p) A)

/-- The valuation-integer tensor lattice cut out inside the log-shell tensor. -/
abbrev TensorIntegerInLogShell :
    Submodule ℤ_[p] (tensorLogShellLattice (p := p) A) :=
  (tensorIntegerLattice (p := p) A).comap
    (tensorLogShellLattice (p := p) A).subtype

theorem tensorIntegerLattice_le_tensorLogShellLattice :
    tensorIntegerLattice (p := p) A ≤ tensorLogShellLattice (p := p) A :=
  tensorIntegerLattice_le_logShellLattice (p := p) A

/-- The tensor Smith basis of the integer sublattice inside the log shell. -/
noncomputable def tensorIntegerBasisN :
    Basis (TensorSmithIndex (p := p) A) ℤ_[p]
      (TensorIntegerInLogShell (p := p) A) :=
  (tensorIntegerBasisO (p := p) A).map
    (Submodule.comapSubtypeEquivOfLe
      (tensorIntegerLattice_le_tensorLogShellLattice (p := p) A)).symm

/-- The product of the local Smith coefficients in a tensor multi-index. -/
noncomputable def tensorSmithCoeff (k : TensorSmithIndex (p := p) A) : ℤ_[p] :=
  ∏ i, localSmithCoeff (p := p) A i (k i)

theorem integralLogTensorEquivLattice_coe_tprod
    (x : (i : ι) → LocalIntegralLogShell (p := p) A i) :
    ((integralLogTensorEquivLattice (p := p) A
        (PiTensorProduct.tprod ℤ_[p] x) : tensorLogShellLattice (p := p) A) :
      FinitePadicTensor (p := p) A) =
      finitePadicTensorTprod (p := p) A (fun i => (x i : A i)) := by
  change integralLogTensorToPadicTensor (p := p) A
    (PiTensorProduct.tprod ℤ_[p] x) = _
  exact integralLogTensorToPadicTensor_tprod (p := p) A x

theorem integerTensorEquivLattice_coe_tprod
    (x : (i : ι) → LocalIntegerLattice (p := p) A i) :
    ((integerTensorEquivLattice (p := p) A
        (PiTensorProduct.tprod ℤ_[p] x) : tensorIntegerLattice (p := p) A) :
      FinitePadicTensor (p := p) A) =
      finitePadicTensorTprod (p := p) A (fun i => (x i : A i)) := by
  change integerTensorToPadicTensor (p := p) A
    (PiTensorProduct.tprod ℤ_[p] x) = _
  exact submoduleTensorMap_tprod (p := p) A _ x

theorem tensorLogShellBasis_apply (k : TensorSmithIndex (p := p) A) :
    (tensorLogShellBasis (p := p) A k : FinitePadicTensor (p := p) A) =
      finitePadicTensorTprod (p := p) A
        (fun i => (localSmithBasisI (p := p) A i (k i) : A i)) := by
  rw [tensorLogShellBasis, Basis.map_apply, Basis.piTensorProduct_apply,
    integralLogTensorEquivLattice_coe_tprod]

theorem tensorIntegerBasisO_apply (k : TensorSmithIndex (p := p) A) :
    (tensorIntegerBasisO (p := p) A k : FinitePadicTensor (p := p) A) =
      finitePadicTensorTprod (p := p) A
        (fun i => (localSmithBasisO (p := p) A i (k i) : A i)) := by
  rw [tensorIntegerBasisO, Basis.map_apply, Basis.piTensorProduct_apply,
    integerTensorEquivLattice_coe_tprod]

theorem tensorIntegerBasisO_apply_eq_prod_smul (k : TensorSmithIndex (p := p) A) :
    (tensorIntegerBasisO (p := p) A k : FinitePadicTensor (p := p) A) =
      tensorSmithCoeff (p := p) A k •
        (tensorLogShellBasis (p := p) A k : FinitePadicTensor (p := p) A) := by
  rw [tensorIntegerBasisO_apply, tensorLogShellBasis_apply, tensorSmithCoeff]
  change PiTensorProduct.tprod ℚ_[p]
      (fun i => (localSmithBasisO (p := p) A i (k i) : A i)) =
    (∏ i, localSmithCoeff (p := p) A i (k i) : ℤ_[p]) •
      PiTensorProduct.tprod ℚ_[p]
        (fun i => (localSmithBasisI (p := p) A i (k i) : A i))
  have hfun : (fun i => (localSmithBasisO (p := p) A i (k i) : A i)) =
      (fun i => localSmithCoeff (p := p) A i (k i) •
        (localSmithBasisI (p := p) A i (k i) : A i)) := by
    funext i
    exact localSmithBasisO_apply (p := p) A i (k i)
  rw [hfun]
  change PiTensorProduct.tprod ℚ_[p]
      (fun i => (localSmithCoeff (p := p) A i (k i) : ℚ_[p]) •
        (localSmithBasisI (p := p) A i (k i) : A i)) =
    ((∏ i, localSmithCoeff (p := p) A i (k i) : ℤ_[p]) : ℚ_[p]) •
      PiTensorProduct.tprod ℚ_[p]
        (fun i => (localSmithBasisI (p := p) A i (k i) : A i))
  rw [show ((∏ i, localSmithCoeff (p := p) A i (k i) : ℤ_[p]) : ℚ_[p]) =
      ∏ i, (localSmithCoeff (p := p) A i (k i) : ℚ_[p]) by
    exact map_prod (algebraMap ℤ_[p] ℚ_[p])
      (fun i => localSmithCoeff (p := p) A i (k i)) Finset.univ]
  exact (PiTensorProduct.tprod ℚ_[p] (s := A)).map_smul_univ
    (fun i => (localSmithCoeff (p := p) A i (k i) : ℚ_[p]))
    (fun i => (localSmithBasisI (p := p) A i (k i) : A i))

theorem tensorIntegerBasisN_apply_eq_prod_smul (k : TensorSmithIndex (p := p) A) :
    (tensorIntegerBasisN (p := p) A k : tensorLogShellLattice (p := p) A) =
      tensorSmithCoeff (p := p) A k • tensorLogShellBasis (p := p) A k := by
  apply Subtype.ext
  rw [Submodule.coe_smul]
  have hNcoe : ((tensorIntegerBasisN (p := p) A k :
      TensorIntegerInLogShell (p := p) A) : tensorLogShellLattice (p := p) A) =
      ⟨(tensorIntegerBasisO (p := p) A k : tensorIntegerLattice (p := p) A),
        tensorIntegerLattice_le_tensorLogShellLattice (p := p) A
          (tensorIntegerBasisO (p := p) A k).property⟩ := by
    rw [tensorIntegerBasisN, Basis.map_apply,
      Submodule.comapSubtypeEquivOfLe_symm_apply]
  have hNval := congrArg (fun x : tensorLogShellLattice (p := p) A =>
    (x : FinitePadicTensor (p := p) A)) hNcoe
  rw [hNval]
  exact tensorIntegerBasisO_apply_eq_prod_smul (p := p) A k

theorem natCard_tensorLogShell_quotient_tensorInteger_eq_prod_span :
    Nat.card (tensorLogShellLattice (p := p) A ⧸
      TensorIntegerInLogShell (p := p) A) =
      ∏ k : TensorSmithIndex (p := p) A,
        Nat.card (ℤ_[p] ⧸
          Ideal.span ({tensorSmithCoeff (p := p) A k} : Set ℤ_[p])) :=
  LeanFormal.IUT.PadicLatticeIndex.natCard_quotient_eq_prod_span_of_smithNormalForm
    (fun k => tensorIntegerBasisN_apply_eq_prod_smul (p := p) A k)

variable [DecidableEq ι]

/-- The tensor integer-exponent formula: the tensor index is the product of the local
indices raised to the products of the ranks of the other local lattices. -/
theorem natCard_tensorLogShell_quotient_tensorInteger_eq_prod_localIndex :
    Nat.card (tensorLogShellLattice (p := p) A ⧸
      TensorIntegerInLogShell (p := p) A) =
      ∏ i, (Nat.card (LocalIntegralLogShell (p := p) A i ⧸
        LocalIntegerInLogShell (p := p) A i)) ^
        (∏ j ∈ Finset.univ.erase i,
          Fintype.card (LocalSmithIndex (p := p) A j)) := by
  classical
  rw [natCard_tensorLogShell_quotient_tensorInteger_eq_prod_span]
  have hfactor : ∀ k : TensorSmithIndex (p := p) A,
      Nat.card (ℤ_[p] ⧸
        Ideal.span ({tensorSmithCoeff (p := p) A k} : Set ℤ_[p])) =
      ∏ i, Nat.card (ℤ_[p] ⧸
        Ideal.span ({localSmithCoeff (p := p) A i (k i)} : Set ℤ_[p])) := by
    intro k
    exact natCard_quotient_span_fintype_prod
      (fun i => localSmithCoeff (p := p) A i (k i))
      (fun i => localSmithCoeff_ne_zero (p := p) A i (k i))
  simp_rw [hfactor]
  let c : (i : ι) → LocalSmithIndex (p := p) A i → ℕ :=
    fun i k => Nat.card (ℤ_[p] ⧸
      Ideal.span ({localSmithCoeff (p := p) A i k} : Set ℤ_[p]))
  change (∏ x : TensorSmithIndex (p := p) A, ∏ i, c i (x i)) = _
  have hprod := prod_pi_prod_eq_prod_pow
    (productIndexFintype := tensorSmithIndexFintype (p := p) A)
    (κ := fun i => LocalSmithIndex (p := p) A i) c
  have hprod' : (∏ x : TensorSmithIndex (p := p) A, ∏ i, c i (x i)) =
      ∏ i, (∏ k, c i k) ^
        (∏ j ∈ Finset.univ.erase i, Fintype.card (LocalSmithIndex (p := p) A j)) := by
    simpa only [TensorSmithIndex] using hprod
  rw [hprod']
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [natCard_localLogShell_quotient_localInteger_eq_prod_span (p := p) A i]

/-- The same formula with the exponent written as the product of the local lattice
ranks `finrank S_j`. -/
theorem natCard_tensorLogShell_quotient_tensorInteger_eq_prod_localIndex_finrank :
    Nat.card (tensorLogShellLattice (p := p) A ⧸
      TensorIntegerInLogShell (p := p) A) =
      ∏ i, (Nat.card (LocalIntegralLogShell (p := p) A i ⧸
        LocalIntegerInLogShell (p := p) A i)) ^
        (∏ j ∈ Finset.univ.erase i,
          Module.finrank ℤ_[p] (LocalIntegralLogShell (p := p) A j)) := by
  classical
  rw [natCard_tensorLogShell_quotient_tensorInteger_eq_prod_localIndex (p := p) A]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  exact (Module.finrank_eq_card_chooseBasisIndex
    (R := ℤ_[p]) (M := LocalIntegralLogShell (p := p) A j)).symm

/-- The same formula with the exponent written as the product of the local field
degrees. -/
theorem natCard_tensorLogShell_quotient_tensorInteger_eq_prod_localIndex_fieldFinrank :
    Nat.card (tensorLogShellLattice (p := p) A ⧸
      TensorIntegerInLogShell (p := p) A) =
      ∏ i, (Nat.card (LocalIntegralLogShell (p := p) A i ⧸
        LocalIntegerInLogShell (p := p) A i)) ^
        (∏ j ∈ Finset.univ.erase i, Module.finrank ℚ_[p] (A j)) := by
  classical
  rw [natCard_tensorLogShell_quotient_tensorInteger_eq_prod_localIndex_finrank
    (p := p) A]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  exact finrank_integralLogShellLattice (K := A j) (p := p)

end

end LeanFormal.IUT.TensorIndexArithmetic
