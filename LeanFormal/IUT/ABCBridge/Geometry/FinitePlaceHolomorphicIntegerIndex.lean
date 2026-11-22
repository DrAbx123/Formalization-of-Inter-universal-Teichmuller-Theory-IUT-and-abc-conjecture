import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegerTensorComparison
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlockFields
import LeanFormal.IUT.Foundations.LocalFields.PadicLatticeIndexFormula
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.DedekindDomain.Different

open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.CompactOpenAddSubgroup
open LeanFormal.IUT.LocalFieldLogarithm LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.FinitePadicIntegralLattice
open Module
open LeanFormal.IUT.PadicLatticeIndex
open scoped LeanFormal.IUT.FinitePadicIntegralLattice
open scoped Matrix

/-!
# The holomorphic integer index as a Smith-normal-form product

The canonical holomorphic unit reference of an actual place-tuple tensor block is the
carrier of an actual `Zp`-submodule. The valuation-integer tensor lattice is contained
in it. Hence the abstract finite index `[O_hol : O_tensor]` is the cardinality of the
corresponding module quotient, and the Smith normal form formula computes it as an
explicit product of powers of `p`.

The final section records, precisely, the remaining comparison with a local
different/discriminant; that comparison is not proved here and the Smith-normal-form
product is not identified with a different formula.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

/-! ## The product unit region is a full rational lattice -/

set_option linter.unusedFintypeInType false in
/-- The unit region of a finite product of local fields spans the whole product over
`Q_p`. Every point is a `p`-power multiple of a point of the unit region. -/
theorem span_padic_unitRegion_eq_top {J : Type*} [Fintype J] {E : J → Type*}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)] :
    Submodule.span ℚ_[p] (unitRegion (K := E) : Set ((j : J) → E j)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨N, hN⟩ :=
    pow_unbounded_of_one_lt (y := (p : ℝ)) ‖x‖
      (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  let c : ℚ_[p] := (p : ℚ_[p]) ^ N
  have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hc_ne : c ≠ 0 := pow_ne_zero N (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hc_norm : ‖c‖ = ((p : ℝ) ^ N)⁻¹ := by
    dsimp only [c]
    rw [norm_pow, Padic.norm_p, ← inv_pow]
  have hy : c • x ∈ unitRegion (K := E) := by
    intro j
    change ‖c • x j‖ ≤ 1
    rw [norm_smul]
    have hlt : ‖c‖ * ‖x j‖ < 1 := by
      calc
        ‖c‖ * ‖x j‖ ≤ ‖c‖ * ‖x‖ :=
          mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) (norm_nonneg _)
        _ < ‖c‖ * (p : ℝ) ^ N := mul_lt_mul_of_pos_left hN (norm_pos_iff.mpr hc_ne)
        _ = 1 := by
          rw [hc_norm, inv_mul_cancel₀ (pow_ne_zero N hp_ne)]
    exact hlt.le
  have hx_eq : x = c⁻¹ • (c • x) := by
    rw [smul_smul, inv_mul_cancel₀ hc_ne, one_smul]
  rw [hx_eq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hy)

/-! ## The holomorphic integer submodule -/

/-- The canonical holomorphic unit reference is the carrier of an actual `Zp`-submodule
of the tuple tensor block, obtained by pulling back the product integer lattice along a
genuine field-product decomposition. -/
theorem exists_arithmeticTupleHolomorphicIntegerSubmodule :
    ∃ H : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple),
      (H : Set (ArithmeticTensorTupleBlock places tuple)) =
        arithmeticTupleCanonicalUnitReference places tuple := by
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  letI : ∀ j, IsUltrametricDist (E j) := fun j => (hE j).2.2
  let integralMap : ArithmeticTensorTupleBlock places tuple →ₗ[ℤ_[p]] ((j : J) → E j) := {
    toFun := e
    map_add' := e.map_add
    map_smul' := fun z x => by
      change e ((z : ℚ_[p]) • x) = (z : ℚ_[p]) • e x
      exact e.toLinearMap.map_smul _ _ }
  refine ⟨(productIntegerLattice (p := p) (E := E)).comap integralMap, ?_⟩
  rw [arithmeticTupleCanonicalUnitReference_eq places tuple e, arithmeticTupleUnitReferencePullback]
  ext x
  change e x ∈ unitRegion (K := E) ↔ x ∈ e.symm '' unitRegion (K := E)
  constructor
  · intro hx
    exact ⟨e x, hx, e.symm_apply_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [AlgEquiv.apply_symm_apply] using hy

/-- The actual holomorphic integer lattice as a `Zp`-submodule. -/
def arithmeticTupleHolomorphicIntegerSubmodule :
    Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple) :=
  Classical.choose (exists_arithmeticTupleHolomorphicIntegerSubmodule places tuple)

/-- Its carrier is exactly the canonical unit reference. -/
theorem coe_arithmeticTupleHolomorphicIntegerSubmodule :
    (arithmeticTupleHolomorphicIntegerSubmodule places tuple :
      Set (ArithmeticTensorTupleBlock places tuple)) =
      arithmeticTupleCanonicalUnitReference places tuple :=
  Classical.choose_spec (exists_arithmeticTupleHolomorphicIntegerSubmodule places tuple)

/-- As an additive subgroup, the holomorphic integer submodule is the existing
decomposition-independent holomorphic integer subgroup. -/
theorem arithmeticTupleHolomorphicIntegerSubmodule_toAddSubgroup_eq :
    (arithmeticTupleHolomorphicIntegerSubmodule places tuple).toAddSubgroup =
      arithmeticTupleHolomorphicIntegerSubgroup places tuple := by
  have hcoe :
      ((arithmeticTupleHolomorphicIntegerSubmodule places tuple).toAddSubgroup :
        Set (ArithmeticTensorTupleBlock places tuple)) =
        (arithmeticTupleHolomorphicIntegerSubgroup places tuple :
          Set (ArithmeticTensorTupleBlock places tuple)) := by
    rw [Submodule.coe_toAddSubgroup, coe_arithmeticTupleHolomorphicIntegerSubmodule,
      (arithmeticTupleHolomorphicIntegerSubgroup_spec places tuple).1]
  apply SetLike.ext
  intro x
  change x ∈ ((arithmeticTupleHolomorphicIntegerSubmodule places tuple).toAddSubgroup :
      Set (ArithmeticTensorTupleBlock places tuple)) ↔
    x ∈ (arithmeticTupleHolomorphicIntegerSubgroup places tuple :
      Set (ArithmeticTensorTupleBlock places tuple))
  rw [hcoe]

/-- The valuation-integer tensor lattice is contained in the holomorphic integer
submodule. -/
theorem arithmeticTupleValuationIntegerLattice_le_holomorphicIntegerSubmodule :
    arithmeticTupleValuationIntegerLattice places tuple ≤
      arithmeticTupleHolomorphicIntegerSubmodule places tuple := by
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  letI : ∀ j, IsUltrametricDist (E j) := fun j => (hE j).2.2
  intro x hx
  have hx' : x ∈ arithmeticTupleCanonicalUnitReference places tuple :=
    arithmeticTupleValuationIntegerLattice_subset_canonicalUnitReference places tuple e hx
  change x ∈ (arithmeticTupleHolomorphicIntegerSubmodule places tuple :
    Set (ArithmeticTensorTupleBlock places tuple))
  rw [coe_arithmeticTupleHolomorphicIntegerSubmodule]
  exact hx'

/-! ## Finiteness, freeness and full rank -/

instance arithmeticTupleHolomorphicIntegerSubmoduleFinite :
    Module.Finite ℤ_[p] (arithmeticTupleHolomorphicIntegerSubmodule places tuple) :=
  finite_of_isCompact (p := p) _
    (by
      rw [coe_arithmeticTupleHolomorphicIntegerSubmodule]
      exact (isCompact_arithmeticTupleCanonicalRegions places tuple).2)

instance arithmeticTupleHolomorphicIntegerSubmoduleFree :
    Module.Free ℤ_[p] (arithmeticTupleHolomorphicIntegerSubmodule places tuple) :=
  free_of_isCompact (p := p) _
    (by
      rw [coe_arithmeticTupleHolomorphicIntegerSubmodule]
      exact (isCompact_arithmeticTupleCanonicalRegions places tuple).2)

/-- The holomorphic integer submodule is a full rational lattice. -/
theorem span_padic_arithmeticTupleHolomorphicIntegerSubmodule_eq_top :
    Submodule.span ℚ_[p] (arithmeticTupleHolomorphicIntegerSubmodule places tuple :
      Set (ArithmeticTensorTupleBlock places tuple)) = ⊤ := by
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  letI : ∀ j, IsUltrametricDist (E j) := fun j => (hE j).2.2
  rw [coe_arithmeticTupleHolomorphicIntegerSubmodule,
    arithmeticTupleCanonicalUnitReference_eq places tuple e,
    arithmeticTupleUnitReferencePullback]
  have hmap : Submodule.span ℚ_[p] (e.symm '' unitRegion (K := E)) =
      Submodule.map e.symm.toLinearMap
        (Submodule.span ℚ_[p] (unitRegion (K := E))) :=
    (Submodule.map_span (e.symm.toLinearMap) (unitRegion (K := E))).symm
  rw [hmap, span_padic_unitRegion_eq_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr e.symm.surjective

/-- The `Zp`-rank of the holomorphic integer submodule is the rational dimension of the
tuple tensor block. -/
theorem arithmeticTupleHolomorphicIntegerSubmodule_finrank_eq :
    Module.finrank ℤ_[p] (arithmeticTupleHolomorphicIntegerSubmodule places tuple) =
      Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) :=
  finrank_of_full_integral_submodule (p := p) _
    (span_padic_arithmeticTupleHolomorphicIntegerSubmodule_eq_top places tuple)

/-- The comap of the valuation-integer tensor lattice into the holomorphic submodule has
the same `Zp`-rank as the holomorphic submodule. -/
theorem arithmeticTupleHolomorphicIntegerSubmodule_comap_finrank_eq :
    Module.finrank ℤ_[p]
      ((arithmeticTupleValuationIntegerLattice places tuple).comap
        (arithmeticTupleHolomorphicIntegerSubmodule places tuple).subtype) =
      Module.finrank ℤ_[p] (arithmeticTupleHolomorphicIntegerSubmodule places tuple) := by
  calc
    Module.finrank ℤ_[p]
        ((arithmeticTupleValuationIntegerLattice places tuple).comap
          (arithmeticTupleHolomorphicIntegerSubmodule places tuple).subtype)
      = Module.finrank ℤ_[p] (arithmeticTupleValuationIntegerLattice places tuple) :=
        (Submodule.comapSubtypeEquivOfLe
          (arithmeticTupleValuationIntegerLattice_le_holomorphicIntegerSubmodule
            places tuple)).finrank_eq
    _ = Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) :=
        finrank_arithmeticTupleValuationIntegerLattice places tuple
    _ = Module.finrank ℤ_[p] (arithmeticTupleHolomorphicIntegerSubmodule places tuple) :=
        (arithmeticTupleHolomorphicIntegerSubmodule_finrank_eq places tuple).symm

/-! ## Alignment with the existing finite intersection index -/

/-- The existing holomorphic intersection index is the cardinality of the module
quotient of the holomorphic submodule by the valuation-integer tensor lattice. -/
theorem arithmeticTupleIntegerTensorHolomorphicIndex_eq_natCard_quotient :
    arithmeticTupleIntegerTensorHolomorphicIndex places tuple =
      Nat.card
        ((arithmeticTupleHolomorphicIntegerSubmodule places tuple) ⧸
          (arithmeticTupleValuationIntegerLattice places tuple).comap
            (arithmeticTupleHolomorphicIntegerSubmodule places tuple).subtype) := by
  unfold arithmeticTupleIntegerTensorHolomorphicIndex intersectionIndex intersectionInLeft
  rw [← arithmeticTupleHolomorphicIntegerSubmodule_toAddSubgroup_eq]
  have hcomap :
      (arithmeticTupleValuationIntegerLattice places tuple).toAddSubgroup.comap
          (arithmeticTupleHolomorphicIntegerSubmodule places tuple).toAddSubgroup.subtype =
        ((arithmeticTupleValuationIntegerLattice places tuple).comap
          (arithmeticTupleHolomorphicIntegerSubmodule places tuple).subtype).toAddSubgroup := rfl
  rw [hcomap]
  rfl

/-- The holomorphic index is the explicit Smith-normal-form product of powers of `p`. -/
theorem arithmeticTupleIntegerTensorHolomorphicIndex_eq_snfProduct :
    arithmeticTupleIntegerTensorHolomorphicIndex places tuple =
      ∏ i, p ^ (Submodule.smithNormalFormCoeffs
        (Module.Free.chooseBasis ℤ_[p]
          (arithmeticTupleHolomorphicIntegerSubmodule places tuple))
        (arithmeticTupleHolomorphicIntegerSubmodule_comap_finrank_eq
          places tuple) i).valuation := by
  rw [arithmeticTupleIntegerTensorHolomorphicIndex_eq_natCard_quotient]
  exact natCard_quotient_eq_prod_pow_valuation_of_finiteFree
    (arithmeticTupleHolomorphicIntegerSubmodule_comap_finrank_eq places tuple)

/-! ## Conductor identity for the trace form -/

/-- Change of the trace discriminant under a diagonal change of a basis family. -/
theorem algebra_discr_diagonal_smul
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b : κ → B) (a : κ → A) :
    Algebra.discr A (fun i => a i • b i) = (∏ i, a i) ^ 2 * Algebra.discr A b := by
  have h := Algebra.discr_of_matrix_vecMul (A := A) (B := B) b (Matrix.diagonal a)
  have hdiag : (Matrix.diagonal a).map (algebraMap A B) =
      Matrix.diagonal (fun i => algebraMap A B (a i)) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, h]
  have hvec : (b ᵥ* (Matrix.diagonal a).map (algebraMap A B)) = fun i => a i • b i := by
    funext i
    rw [hdiag, Matrix.vecMul_diagonal]
    simp [Algebra.smul_def, mul_comm]
  rw [hvec, Matrix.det_diagonal] at h
  exact h

/-- The trace-form discriminant of a `Zp`-basis of a submodule inside the tuple tensor
block. -/
def arithmeticTupleLatticeDiscriminant
    (L : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple))
    {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ ℤ_[p] L) : ℚ_[p] :=
  Algebra.discr ℚ_[p]
    (fun i => ((b i : L) : ArithmeticTensorTupleBlock places tuple))

/-- Conductor identity: if a basis of the valuation-integer tensor lattice is the
diagonal `a`-multiple of a basis of the holomorphic integer submodule, then the
trace-form discriminant of the tensor lattice is `(∏ a)^2` times the discriminant of
the holomorphic lattice. -/
theorem arithmeticTupleValuationIntegerLattice_discriminant_eq_prod_sq_mul
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b : Basis κ ℤ_[p] (arithmeticTupleHolomorphicIntegerSubmodule places tuple))
    (bT : Basis κ ℤ_[p] (arithmeticTupleValuationIntegerLattice places tuple))
    (a : κ → ℤ_[p])
    (hbT : ∀ i,
      ((bT i : arithmeticTupleValuationIntegerLattice places tuple) :
          ArithmeticTensorTupleBlock places tuple) =
        (a i : ℚ_[p]) •
          ((b i : arithmeticTupleHolomorphicIntegerSubmodule places tuple) :
            ArithmeticTensorTupleBlock places tuple)) :
    arithmeticTupleLatticeDiscriminant places tuple
        (arithmeticTupleValuationIntegerLattice places tuple) bT =
      (∏ i, (a i : ℚ_[p])) ^ 2 *
        arithmeticTupleLatticeDiscriminant places tuple
          (arithmeticTupleHolomorphicIntegerSubmodule places tuple) b := by
  have h := algebra_discr_diagonal_smul (A := ℚ_[p])
    (B := ArithmeticTensorTupleBlock places tuple)
    (b := fun i =>
      ((b i : arithmeticTupleHolomorphicIntegerSubmodule places tuple) :
        ArithmeticTensorTupleBlock places tuple))
    (a := fun i => (a i : ℚ_[p]))
  unfold arithmeticTupleLatticeDiscriminant
  rw [← h]
  exact congrArg (fun family => Algebra.discr ℚ_[p] family) (funext hbT)

/-- The Smith-normal-form conductor identity for the holomorphic pair: the trace
discriminant of the valuation-integer tensor lattice is the squared product of the
Smith-normal-form coefficients times the trace discriminant of the holomorphic
integer submodule. -/
theorem arithmeticTupleHolomorphic_conductor_identity_snf
    (h : Module.finrank ℤ_[p]
      ((arithmeticTupleValuationIntegerLattice places tuple).comap
        (arithmeticTupleHolomorphicIntegerSubmodule places tuple).subtype) =
      Module.finrank ℤ_[p] (arithmeticTupleHolomorphicIntegerSubmodule places tuple)) :
    arithmeticTupleLatticeDiscriminant places tuple
        (arithmeticTupleValuationIntegerLattice places tuple)
        ((Submodule.smithNormalFormBotBasis
          (Module.Free.chooseBasis ℤ_[p]
            (arithmeticTupleHolomorphicIntegerSubmodule places tuple)) h).map
          (Submodule.comapSubtypeEquivOfLe
            (arithmeticTupleValuationIntegerLattice_le_holomorphicIntegerSubmodule
              places tuple))) =
      (∏ i, ((Submodule.smithNormalFormCoeffs
          (Module.Free.chooseBasis ℤ_[p]
            (arithmeticTupleHolomorphicIntegerSubmodule places tuple)) h i : ℤ_[p]) : ℚ_[p])) ^ 2 *
        arithmeticTupleLatticeDiscriminant places tuple
          (arithmeticTupleHolomorphicIntegerSubmodule places tuple)
          (Submodule.smithNormalFormTopBasis
            (Module.Free.chooseBasis ℤ_[p]
              (arithmeticTupleHolomorphicIntegerSubmodule places tuple)) h) := by
  apply arithmeticTupleValuationIntegerLattice_discriminant_eq_prod_sq_mul
  intro i
  change ((Submodule.comapSubtypeEquivOfLe
      (arithmeticTupleValuationIntegerLattice_le_holomorphicIntegerSubmodule places tuple)
      (Submodule.smithNormalFormBotBasis
        (Module.Free.chooseBasis ℤ_[p]
          (arithmeticTupleHolomorphicIntegerSubmodule places tuple)) h i) :
        arithmeticTupleValuationIntegerLattice places tuple) :
      ArithmeticTensorTupleBlock places tuple) =
    ((Submodule.smithNormalFormCoeffs
      (Module.Free.chooseBasis ℤ_[p]
        (arithmeticTupleHolomorphicIntegerSubmodule places tuple)) h i : ℤ_[p]) : ℚ_[p]) •
      ((Submodule.smithNormalFormTopBasis
        (Module.Free.chooseBasis ℤ_[p]
          (arithmeticTupleHolomorphicIntegerSubmodule places tuple)) h i :
          arithmeticTupleHolomorphicIntegerSubmodule places tuple) :
        ArithmeticTensorTupleBlock places tuple)
  rw [Submodule.comapSubtypeEquivOfLe_apply_coe, Submodule.smithNormalFormBotBasis_def]
  rfl

/-! ## The precise different/discriminant interface -/

/-- The precise remaining different/discriminant interface.

For every finite field-product decomposition `e` of the tuple tensor block and every
choice of integral models `O j` of the field factors `E j` (commutative Dedekind
domains, `Zp`-algebras, integral closures of `Zp` in `E j`, torsion-free over `Zp`),
the holomorphic index is the product of the quotient cardinalities of the local
relative different ideals `differentIdeal ℤ_[p] (O j)`.

This is a specification only.  The file does not construct the integral models, does
not supply the Dedekind-domain instances, and does not prove that the Smith-normal-form
exponents coincide with the local different exponents.  In particular the proved
Smith-normal-form product above is not identified with a different formula. -/
def ArithmeticTupleHolomorphicDifferentInterface
    (J : Type (max u v)) [Fintype J] (E : J → Type (max u v))
    [∀ j, NontriviallyNormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    [∀ j, IsUltrametricDist (E j)]
    [∀ j, Algebra ℤ_[p] (E j)] [∀ j, IsScalarTower ℤ_[p] ℚ_[p] (E j)]
    (_e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)) : Prop :=
  ∀ (O : J → Type (max u v)) [∀ j, CommRing (O j)] [∀ j, IsDedekindDomain (O j)]
    [∀ j, Algebra ℤ_[p] (O j)] [∀ j, Algebra (O j) (E j)]
    [∀ j, IsScalarTower ℤ_[p] (O j) (E j)]
    [∀ j, IsIntegralClosure (O j) ℤ_[p] (E j)]
    [∀ j, IsTorsionFree ℤ_[p] (O j)],
    arithmeticTupleIntegerTensorHolomorphicIndex places tuple =
      ∏ j, Submodule.cardQuot (differentIdeal ℤ_[p] (O j))
end

end LeanFormal.IUT.NumberFieldFinitePlace














