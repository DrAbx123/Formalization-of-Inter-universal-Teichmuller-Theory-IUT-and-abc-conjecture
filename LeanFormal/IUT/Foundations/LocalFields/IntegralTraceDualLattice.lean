import LeanFormal.IUT.Foundations.LocalFields.FinitePadicIntegralLattice
import LeanFormal.IUT.Foundations.LocalFields.PadicLatticeIndexFormula
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.RingTheory.DedekindDomain.Different

/-!
# Integral trace dual lattices

For a commutative ring `R` with fraction field `S`, an `S`-vector space `M`,
and a bilinear form `B : M →ₗ[S] M →ₗ[S] S`, the integral dual of an
`R`-submodule `L` is

`L* = {x | ∀ y ∈ L, B x y ∈ R}`.

This file defines that submodule as `integralTraceDualLattice B L` using
Mathlib's `LinearMap.BilinForm.dualSubmodule`, records the elementary order
and duality properties, and specializes to `R = ℤ_[p]`, `S = ℚ_[p]`.
For a lattice spanned by a `ℚ_[p]`-basis it is the `ℤ_[p]`-span of the
`B`-dual basis; consequently it is finite free of the same rank.

The final sections connect this construction to Mathlib's
`Submodule.traceDual A K I` (which is definitionally the same dual under the
multiplicative trace form) and to `differentIdeal A B`. This is the local
trace-pairing input needed by the different/discriminant decomposition of
`[O_hol : O_tensor]`; the file does not construct the actual different ideal
of a completed number field, and the `ℤ_[p]`-algebra structure on
`Integers K` is kept as an explicit hypothesis.
-/

namespace LeanFormal.IUT.IntegralTraceDual

open scoped LeanFormal.IUT.FinitePadicIntegralLattice
open scoped nonZeroDivisors
open LeanFormal.IUT.FinitePadicIntegralLattice
open LeanFormal.IUT.PadicLatticeIndex
open Module

noncomputable section

universe u v w

/-! ## General integral dual under a bilinear form -/

variable {R S M : Type*} [CommRing R] [Field S] [AddCommGroup M]
  [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]

/-- The integral dual of `L` with respect to `B`: the elements `x : M` whose
`B`-pairing with every element of `L` is integral. -/
def integralTraceDualLattice (B : LinearMap.BilinForm S M)
    (L : Submodule R M) : Submodule R M :=
  B.dualSubmodule L

/-- Characteristic membership: `x` lies in the integral dual exactly when all
its pairings with `L` lie in the unit submodule `R ⊆ S`. -/
theorem mem_integralTraceDualLattice_iff
    {B : LinearMap.BilinForm S M} {L : Submodule R M} {x : M} :
    x ∈ integralTraceDualLattice B L ↔
      ∀ y ∈ L, B x y ∈ (1 : Submodule R S) :=
  Iff.rfl

/-- Membership in the integral dual in terms of an actual `R`-lift. -/
theorem mem_integralTraceDualLattice_iff_exists
    {B : LinearMap.BilinForm S M} {L : Submodule R M} {x : M} :
    x ∈ integralTraceDualLattice B L ↔
      ∀ y ∈ L, ∃ z : R, algebraMap R S z = B x y := by
  rw [mem_integralTraceDualLattice_iff]
  constructor
  · intro h y hy
    exact Submodule.mem_one.mp (h y hy)
  · intro h y hy
    exact Submodule.mem_one.mpr (h y hy)

/-- The integral dual is antitone in the lattice. -/
theorem integralTraceDualLattice_antitone (B : LinearMap.BilinForm S M) :
    Antitone (integralTraceDualLattice (R := R) (S := S) (M := M) B) := by
  intro L₁ L₂ hL x hx
  rw [mem_integralTraceDualLattice_iff] at hx ⊢
  exact fun y hy => hx y (hL hy)

/-- Orthogonality duality of integral duals. -/
theorem le_flip_integralTraceDualLattice
    {B : LinearMap.BilinForm S M} {L₁ L₂ : Submodule R M} :
    L₁ ≤ integralTraceDualLattice B.flip L₂ ↔
      L₂ ≤ integralTraceDualLattice B L₁ := by
  constructor
  · intro h x hx y hy
    simpa only [LinearMap.BilinForm.flip_apply] using h hy x hx
  · intro h x hx y hy
    simpa only [LinearMap.BilinForm.flip_apply] using h hy x hx

/-- For the lattice spanned by an `S`-basis, the integral dual is the
`R`-span of the `B`-dual basis. -/
theorem integralTraceDualLattice_span_basis
    {ι : Type*} [Finite ι] [DecidableEq ι]
    (B : LinearMap.BilinForm S M) (hB : B.Nondegenerate)
    (b : Module.Basis ι S M) :
    integralTraceDualLattice B (Submodule.span R (Set.range b)) =
      Submodule.span R (Set.range (B.dualBasis hB b)) :=
  LinearMap.BilinForm.dualSubmodule_span_of_basis B hB b

/-! ## The `ℤ_[p]`-lattice specialization -/

variable {p : ℕ} [Fact p.Prime]
variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℚ_[p] M]

/-- The `ℤ_[p]`-integral trace dual lattice. -/
abbrev padicIntegralTraceDualLattice (B : LinearMap.BilinForm ℚ_[p] M)
    (L : Submodule ℤ_[p] M) : Submodule ℤ_[p] M :=
  integralTraceDualLattice (R := ℤ_[p]) (S := ℚ_[p]) B L

theorem mem_padicIntegralTraceDualLattice_iff
    {B : LinearMap.BilinForm ℚ_[p] M} {L : Submodule ℤ_[p] M} {x : M} :
    x ∈ padicIntegralTraceDualLattice B L ↔
      ∀ y ∈ L, B x y ∈ (1 : Submodule ℤ_[p] ℚ_[p]) :=
  mem_integralTraceDualLattice_iff

theorem padicIntegralTraceDualLattice_span_basis
    {ι : Type*} [Finite ι] [DecidableEq ι]
    (B : LinearMap.BilinForm ℚ_[p] M) (hB : B.Nondegenerate)
    (b : Module.Basis ι ℚ_[p] M) :
    padicIntegralTraceDualLattice B (basisIntegralLattice b) =
      Submodule.span ℤ_[p] (Set.range (B.dualBasis hB b)) :=
  integralTraceDualLattice_span_basis B hB b

/-- The lattice spanned by a `ℚ_[p]`-basis is finite over `ℤ_[p]`. -/
theorem basisIntegralLattice_moduleFinite {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℚ_[p] M) :
    Module.Finite ℤ_[p] (basisIntegralLattice b) :=
  Module.Finite.of_basis (b.restrictScalars ℤ_[p])

/-- The lattice spanned by a `ℚ_[p]`-basis is free over `ℤ_[p]`. -/
theorem basisIntegralLattice_moduleFree {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℚ_[p] M) :
    Module.Free ℤ_[p] (basisIntegralLattice b) :=
  Module.Free.of_basis (b.restrictScalars ℤ_[p])

/-- The rank of the lattice spanned by a `ℚ_[p]`-basis is the number of
basis vectors. -/
theorem finrank_basisIntegralLattice {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℚ_[p] M) :
    Module.finrank ℤ_[p] (basisIntegralLattice b) = Fintype.card ι := by
  letI := basisIntegralLattice_moduleFinite b
  letI := basisIntegralLattice_moduleFree b
  exact Module.finrank_eq_card_basis (b.restrictScalars ℤ_[p])

/-- The trace dual of a basis lattice is finite over `ℤ_[p]`. -/
theorem padicIntegralTraceDualLattice_moduleFinite
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm ℚ_[p] M) (hB : B.Nondegenerate)
    (b : Module.Basis ι ℚ_[p] M) :
    Module.Finite ℤ_[p] (padicIntegralTraceDualLattice B (basisIntegralLattice b)) := by
  rw [padicIntegralTraceDualLattice_span_basis B hB b]
  exact basisIntegralLattice_moduleFinite (B.dualBasis hB b)

/-- The trace dual of a basis lattice is free over `ℤ_[p]`. -/
theorem padicIntegralTraceDualLattice_moduleFree
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm ℚ_[p] M) (hB : B.Nondegenerate)
    (b : Module.Basis ι ℚ_[p] M) :
    Module.Free ℤ_[p] (padicIntegralTraceDualLattice B (basisIntegralLattice b)) := by
  rw [padicIntegralTraceDualLattice_span_basis B hB b]
  exact basisIntegralLattice_moduleFree (B.dualBasis hB b)

/-- The trace dual of a basis lattice has the same rank as `M`. -/
theorem finrank_padicIntegralTraceDualLattice
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm ℚ_[p] M) (hB : B.Nondegenerate)
    (b : Module.Basis ι ℚ_[p] M) :
    Module.finrank ℤ_[p] (padicIntegralTraceDualLattice B (basisIntegralLattice b)) =
      Module.finrank ℚ_[p] M := by
  rw [padicIntegralTraceDualLattice_span_basis B hB b]
  letI := basisIntegralLattice_moduleFinite (B.dualBasis hB b)
  letI := basisIntegralLattice_moduleFree (B.dualBasis hB b)
  change Module.finrank ℤ_[p] (basisIntegralLattice (B.dualBasis hB b)) =
    Module.finrank ℚ_[p] M
  rw [finrank_basisIntegralLattice (B.dualBasis hB b)]
  exact (Module.finrank_eq_card_basis b).symm

/-- The trace dual of a basis lattice is full rank. -/
theorem span_padicIntegralTraceDualLattice_eq_top
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm ℚ_[p] M) (hB : B.Nondegenerate)
    (b : Module.Basis ι ℚ_[p] M) :
    Submodule.span ℚ_[p]
      (padicIntegralTraceDualLattice B (basisIntegralLattice b) : Set M) = ⊤ := by
  rw [padicIntegralTraceDualLattice_span_basis B hB b]
  rw [Submodule.span_span_of_tower]
  exact (B.dualBasis hB b).span_eq

/-! ## The quotient index as the valuation of a determinant -/

/-- A unit of `ℤ_[p]` has valuation zero. -/
theorem padicInt_valuation_unit (u : ℤ_[p]ˣ) : (u : ℤ_[p]).valuation = 0 := by
  have h := PadicInt.valuation_mul (p := p) (x := (u : ℤ_[p]))
    (y := ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) (Units.ne_zero u) (Units.ne_zero u⁻¹)
  have h' : 0 = (u : ℤ_[p]).valuation + ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]).valuation := by
    simpa using h
  omega

/-- Associated elements of `ℤ_[p]` have the same valuation. -/
theorem padicInt_valuation_eq_of_associated {a b : ℤ_[p]} (h : Associated a b) :
    a.valuation = b.valuation := by
  rcases h with ⟨u, rfl⟩
  by_cases ha : a = 0
  · simp [ha]
  · rw [PadicInt.valuation_mul ha (Units.ne_zero u), padicInt_valuation_unit u, add_zero]

/-- The valuation of a finite product of nonzero elements is the sum of the
valuations. -/
theorem padicInt_valuation_prod {ι : Type*} (s : Finset ι) (a : ι → ℤ_[p])
    (ha : ∀ i ∈ s, a i ≠ 0) :
    (s.prod a).valuation = s.sum (fun i => (a i).valuation) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      PadicInt.valuation_mul (ha i (Finset.mem_insert_self i s))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => ha j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))]

/-- For a finite free `ℤ_[p]`-module `M` and a finite-rank submodule `N`, the
cardinality of `M ⧸ N` is `p` raised to the valuation of the determinant of
the inclusion composed with any linear equivalence `M ≃ N`. -/
theorem natCard_quotient_eq_pow_valuation_det_equiv
    {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M]
    (N : Submodule ℤ_[p] M) (e : M ≃ₗ[ℤ_[p]] N) :
    Nat.card (M ⧸ N) =
      p ^ (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[ℤ_[p]] N))).valuation := by
  classical
  let b := Module.Free.chooseBasis ℤ_[p] M
  have h : Module.finrank ℤ_[p] N = Module.finrank ℤ_[p] M := e.symm.finrank_eq
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[ℤ_[p]] N := b'.equiv ab (Equiv.refl _)
  let f : M →ₗ[ℤ_[p]] M := N.subtype.comp (e' : M →ₗ[ℤ_[p]] N)
  have hf : ∀ i, f (b' i) = a i • b' i := by
    intro i
    have h1 : f (b' i) = (ab i : M) := by
      simp [f, e']
    rw [h1]
    exact ab_eq i
  have hmat : LinearMap.toMatrix b' b' f = Matrix.diagonal a := by
    ext i j
    rw [LinearMap.toMatrix_apply, hf, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hdet : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b' f, hmat, Matrix.det_diagonal]
  have hcard : Nat.card (M ⧸ N) = ∏ i, p ^ (a i).valuation :=
    natCard_quotient_eq_prod_pow_valuation_of_smithNormalForm ab_eq
  have hsum : (∏ i, a i).valuation = ∑ i, (a i).valuation :=
    padicInt_valuation_prod Finset.univ a
      (fun i _ => Submodule.smithNormalFormCoeffs_ne_zero b h i)
  have hprod : (∏ i, p ^ (a i).valuation) = p ^ (∏ i, a i).valuation := by
    rw [Finset.prod_pow_eq_pow_sum, hsum]
  have hassoc : Associated (LinearMap.det f)
      (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[ℤ_[p]] N))) :=
    LinearMap.associated_det_comp_equiv N.subtype e' e
  rw [hcard, hprod, ← hdet, padicInt_valuation_eq_of_associated hassoc]

/-- The Gram matrix of a basis, as a matrix over `ℤ_[p]`, when the trace dual
contains the basis lattice. -/
noncomputable def traceDualGramMatrix
    {ι : Type*} (B : LinearMap.BilinForm ℚ_[p] M) (hB : B.Nondegenerate)
    (b : Module.Basis ι ℚ_[p] M)
    (hle : basisIntegralLattice b ≤
      padicIntegralTraceDualLattice B (basisIntegralLattice b)) :
    Matrix ι ι ℤ_[p] :=
  Matrix.of fun i j =>
    Classical.choose (Submodule.mem_one.mp
      ((mem_padicIntegralTraceDualLattice_iff).mp
        (hle (Submodule.subset_span ⟨i, rfl⟩))
        (b j) (Submodule.subset_span ⟨j, rfl⟩)))

/-- The entries of the integral Gram matrix are the values of the bilinear
form on the basis. -/
theorem traceDualGramMatrix_apply
    {ι : Type*} (B : LinearMap.BilinForm ℚ_[p] M) (hB : B.Nondegenerate)
    (b : Module.Basis ι ℚ_[p] M)
    (hle : basisIntegralLattice b ≤
      padicIntegralTraceDualLattice B (basisIntegralLattice b)) (i j : ι) :
    ((traceDualGramMatrix B hB b hle i j : ℤ_[p]) : ℚ_[p]) = B (b i) (b j) := by
  have h := Classical.choose_spec (Submodule.mem_one.mp
    ((mem_padicIntegralTraceDualLattice_iff).mp
      (hle (Submodule.subset_span ⟨i, rfl⟩))
      (b j) (Submodule.subset_span ⟨j, rfl⟩)))
  simpa [traceDualGramMatrix, PadicInt.algebraMap_apply] using h

/-- If the trace-dual lattice `L*` contains the basis lattice `L = span b`,
then the index `[L* : L]` is `p` raised to the valuation of the determinant
of the integral Gram matrix `(B (b i) (b j))`.  The containment `L ≤ L*` is
exactly the integrality of the form on `L`. -/
theorem natCard_traceDual_quotient_eq_pow_valuation_gram_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm ℚ_[p] M) (hB : B.Nondegenerate)
    (b : Module.Basis ι ℚ_[p] M)
    (hle : basisIntegralLattice b ≤
      padicIntegralTraceDualLattice B (basisIntegralLattice b)) :
    Nat.card (↥(padicIntegralTraceDualLattice B (basisIntegralLattice b)) ⧸
        Submodule.comap
          (padicIntegralTraceDualLattice B (basisIntegralLattice b)).subtype
          (basisIntegralLattice b)) =
      p ^ (traceDualGramMatrix B hB b hle).det.valuation := by
  classical
  let bstar := B.dualBasis hB b
  let bstarL : Module.Basis ι ℤ_[p] ↥(basisIntegralLattice bstar) :=
    bstar.restrictScalars ℤ_[p]
  have hspan : basisIntegralLattice bstar =
      padicIntegralTraceDualLattice B (basisIntegralLattice b) := by
    simpa [bstar, basisIntegralLattice] using
      (padicIntegralTraceDualLattice_span_basis B hB b).symm
  have hle' : basisIntegralLattice b ≤ basisIntegralLattice bstar := by
    rw [hspan]
    exact hle
  rw [padicIntegralTraceDualLattice_span_basis B hB b]
  let N : Submodule ℤ_[p] ↥(basisIntegralLattice bstar) :=
    Submodule.comap (basisIntegralLattice bstar).subtype (basisIntegralLattice b)
  let eNL : N ≃ₗ[ℤ_[p]] basisIntegralLattice b :=
    Submodule.comapSubtypeEquivOfLe hle'
  let bL : Module.Basis ι ℤ_[p] ↥(basisIntegralLattice b) :=
    b.restrictScalars ℤ_[p]
  let bN : Module.Basis ι ℤ_[p] N :=
    bL.map eNL.symm
  let e : ↥(basisIntegralLattice bstar) ≃ₗ[ℤ_[p]] N :=
    bstarL.equiv bN (Equiv.refl ι)
  letI : Module.Free ℤ_[p] ↥(basisIntegralLattice bstar) :=
    basisIntegralLattice_moduleFree bstar
  letI : Module.Finite ℤ_[p] ↥(basisIntegralLattice bstar) :=
    basisIntegralLattice_moduleFinite bstar
  letI : Module.Free ℤ_[p] N :=
    Module.Free.of_equiv' (basisIntegralLattice_moduleFree b) eNL.symm
  letI : Module.Finite ℤ_[p] N :=
    (Module.Finite.equiv_iff eNL.symm).mp (basisIntegralLattice_moduleFinite b)
  let f : ↥(basisIntegralLattice bstar) →ₗ[ℤ_[p]]
      ↥(basisIntegralLattice bstar) :=
    N.subtype ∘ₗ (e : ↥(basisIntegralLattice bstar) →ₗ[ℤ_[p]] N)
  have hcard :
      Nat.card (↥(basisIntegralLattice bstar) ⧸ N) =
        p ^ (LinearMap.det f).valuation := by
    simpa only [f] using natCard_quotient_eq_pow_valuation_det_equiv N e
  change Nat.card (↥(basisIntegralLattice bstar) ⧸ N) = _
  rw [hcard]
  congr 1
  have hmat : LinearMap.toMatrix bstarL bstarL f =
      Matrix.transpose (traceDualGramMatrix B hB b hle) := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.transpose_apply]
    apply Subtype.coe_injective
    change (((bstar.restrictScalars ℤ_[p]).repr
        (f (bstarL j))) i : ℚ_[p]) =
      (traceDualGramMatrix B hB b hle j i : ℚ_[p])
    rw [traceDualGramMatrix_apply]
    have hcoe : ((f (bstarL j) :
        ↥(basisIntegralLattice bstar)) : M) = b j := by
      change ((e (bstarL j) : ↥N) : M) = b j
      dsimp only [e, bN, eNL]
      rw [Basis.equiv_apply, Basis.map_apply,
        Submodule.comapSubtypeEquivOfLe_symm_apply]
      dsimp only [bL]
      rw [Equiv.refl_apply]
      change (((b.restrictScalars ℤ_[p] :
        Module.Basis ι ℤ_[p] (basisIntegralLattice b)) j :
          basisIntegralLattice b) : M) = b j
      exact Module.Basis.restrictScalars_apply (R := ℤ_[p]) (b := b) j
    have hrepr : (((bstar.restrictScalars ℤ_[p]).repr
        (f (bstarL j))) i : ℚ_[p]) =
        (bstar.repr (f (bstarL j))) i := by
      simpa only [PadicInt.algebraMap_apply] using
        Basis.restrictScalars_repr_apply (R := ℤ_[p]) (S := ℚ_[p])
          (b := bstar) (f (bstarL j)) i
    rw [hrepr, hcoe, LinearMap.BilinForm.dualBasis_repr_apply hB b (b j) i]
  have hdet : LinearMap.det f =
      Matrix.det (LinearMap.toMatrix bstarL bstarL f) :=
    (LinearMap.det_toMatrix bstarL f).symm
  rw [hdet, hmat, Matrix.det_transpose]

/-! ## Bridge to Mathlib's `Submodule.traceDual` -/

section TraceForm

variable {A K B L : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]

/-- The integral dual of the multiplicative trace form is Mathlib's
`Submodule.traceDual`, restricted to the base ring. -/
theorem integralTraceDualLattice_traceForm_eq_traceDual
    (I : Submodule B L) :
    integralTraceDualLattice (R := A) (S := K) (Algebra.traceForm K L)
        (I.restrictScalars A) =
      (Submodule.traceDual A K I).restrictScalars A := by
  rw [Submodule.restrictScalars_traceDual]
  rfl

/-- Membership form of the trace-form bridge. -/
theorem mem_traceDual_iff_traceForm_mem
    {I : Submodule B L} {x : L} :
    x ∈ Submodule.traceDual A K I ↔
      ∀ y ∈ I, Algebra.traceForm K L x y ∈ (algebraMap A K).range :=
  Submodule.mem_traceDual

/-- If `I` is contained in the trace dual of `J`, then the product `I * J`
is trace-integral. -/
theorem mul_le_traceDual_one_of_le_traceDual
    {I J : Submodule B L} (h : I ≤ Submodule.traceDual A K J) :
    I * J ≤ Submodule.traceDual A K 1 :=
  Submodule.le_traceDual.mp h

end TraceForm

/-! ## The different ideal -/

section Different

variable {A K B L : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L]
  [Algebra.IsSeparable K L] [IsIntegralClosure B A L] [IsIntegrallyClosed A]
  [IsDedekindDomain B] [Module.IsTorsionFree A B] [IsFractionRing B L]

/-- The different ideal is the inverse of the trace dual of the unit ideal,
as a submodule of `L`. -/
theorem coeSubmodule_differentIdeal_eq_inv_traceDual :
    IsLocalization.coeSubmodule L (differentIdeal A B) =
      1 / Submodule.traceDual A K 1 :=
  coeSubmodule_differentIdeal A K B

/-- Criterion for divisibility by the different ideal in terms of the trace
form on the inverse fractional ideal. -/
theorem differentIdeal_le_iff_traceForm_le_one
    {I : Ideal B} (hI : I ≠ ⊥) :
    differentIdeal A B ≤ I ↔
      Submodule.map ((Algebra.trace K L).restrictScalars A)
        (Submodule.restrictScalars A
          ((I⁻¹ : FractionalIdeal B⁰ L) : Submodule B L)) ≤ 1 :=
  differentialIdeal_le_iff (A := A) (K := K) (L := L) (B := B) hI

end Different

end

end LeanFormal.IUT.IntegralTraceDual
