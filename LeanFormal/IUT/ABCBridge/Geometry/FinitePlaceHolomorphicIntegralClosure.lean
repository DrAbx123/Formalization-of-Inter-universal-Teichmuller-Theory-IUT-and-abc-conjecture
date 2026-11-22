import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicIntegralLattice
import LeanFormal.IUT.Foundations.LocalFields.ProductIntegerLattice
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# The canonical holomorphic unit reference is a `Zp`-integral lattice

This file proves the `O_hol` interface for IUT IV, Section 1, Proposition 1.1:
the actual canonical holomorphic unit reference of a place-tuple tensor block is
the integral closure of `Zp` in that block.  This is the integrality input for
the index `arithmeticTupleIntegerTensorHolomorphicIndex = [O_hol : O_tensor]`.

The argument has two independent halves.

* Forward: for a finite family of finite-dimensional proper ultrametric normed
  fields over `Qp`, the product unit region `{x | forall j, ||x j|| <= 1}` is a
  compact `Zp`-subalgebra.  A compact `Zp`-submodule of a finite-dimensional
  `Qp`-space is finitely generated (`FinitePadicIntegralLattice.finite_of_isCompact`),
  and an element of a finitely generated `Zp`-subalgebra is integral
  (`IsIntegral.of_mem_of_fg`).  Transporting along a genuine field-product
  decomposition proves `O_hol` is contained in the integral closure.
* Reverse: if `x` in a finite-dimensional ultrametric extension of `Qp` is
  integral over `Zp`, then `||x|| <= 1`.  The unit ball is the integer ring of
  `NormedField.valuation`, hence integrally closed in the field, and `Zp` maps
  into it because the norm of a `Qp`-scalar is its `Qp`-norm.  Applying this to
  the decomposition coordinates proves the reverse inclusion, hence equality.

No trace pairing, discriminant, integral model, or index hypothesis is used.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldProductHull

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Finite ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

open scoped LeanFormal.IUT.FinitePadicIntegralLattice

/-- The `Zp`-algebra structure on the actual tuple tensor block inherited from
the scalar tower `Zp -> Qp -> Q`. -/
instance arithmeticTensorTupleZpAlgebra :
    Algebra ℤ_[p] (ArithmeticTensorTupleBlock places tuple) :=
  Algebra.restrictScalars ℤ_[p] ℚ_[p] (ArithmeticTensorTupleBlock places tuple)

/-- The `Zp`-scalar structure on the actual tuple tensor block is compatible
with its `Qp`-scalar structure. -/
instance arithmeticTensorTupleZpIsScalarTower :
    IsScalarTower ℤ_[p] ℚ_[p] (ArithmeticTensorTupleBlock places tuple) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

section ProductUnitRegion

variable {J : Type*} [Finite J] {E : J → Type*}
  [∀ j, NontriviallyNormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
  [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
  [∀ j, IsUltrametricDist (E j)]

/-- The product of the `Qp`-algebras `E j` is a `Zp`-algebra through
`Zp -> Qp -> product E j`. -/
local instance productUnitRegionZpAlgebra :
    Algebra ℤ_[p] ((j : J) → E j) :=
  Algebra.restrictScalars ℤ_[p] ℚ_[p] ((j : J) → E j)

/-- Every element of the product unit region is integral over `Zp`.

The unit region is the carrier of a `Zp`-subalgebra of the finite-dimensional
`Qp`-space `product E j`.  It is compact because each `E j` is proper, so it is
a finitely generated `Zp`-module, and an element of a finitely generated
subalgebra is integral. -/
theorem isIntegral_of_mem_productUnitRegion
    {x : (j : J) → E j} (hx : x ∈ unitRegion (K := E)) :
    IsIntegral ℤ_[p] x := by
  classical
  letI : Fintype J := Fintype.ofFinite J
  letI : ∀ j, Algebra ℤ_[p] (E j) := fun j => Algebra.restrictScalars ℤ_[p] ℚ_[p] (E j)
  have halgMap (z : ℤ_[p]) (j : J) :
      algebraMap ℤ_[p] ((j : J) → E j) z j = algebraMap ℤ_[p] (E j) z := rfl
  let S : Subalgebra ℤ_[p] ((j : J) → E j) :=
    { carrier := unitRegion (K := E)
      zero_mem' := by intro j; simp
      one_mem' := by intro j; simp
      add_mem' := by
        intro a b ha hb j
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha j) (hb j))
      mul_mem' := by
        intro a b ha hb j
        change ‖a j * b j‖ ≤ 1
        rw [norm_mul]
        exact mul_le_one₀ (ha j) (norm_nonneg _) (hb j)
      algebraMap_mem' := by
        intro z j
        rw [halgMap]
        calc ‖algebraMap ℤ_[p] (E j) z‖
            = ‖algebraMap ℚ_[p] (E j) (algebraMap ℤ_[p] ℚ_[p] z)‖ := rfl
          _ = ‖algebraMap ℤ_[p] ℚ_[p] z‖ := norm_algebraMap' _ _
          _ = ‖z‖ := PadicInt.norm_def
          _ ≤ 1 := z.property }
  have hcompact : IsCompact (S : Set ((j : J) → E j)) := by
    change IsCompact (unitRegion (K := E))
    exact isCompact_unitRegion
  have hfinite : Module.Finite ℤ_[p] S.toSubmodule :=
    LeanFormal.IUT.FinitePadicIntegralLattice.finite_of_isCompact (p := p)
      S.toSubmodule hcompact
  have hfg : S.toSubmodule.FG := Module.Finite.iff_fg.mp hfinite
  exact IsIntegral.of_mem_of_fg S hfg x hx

end ProductUnitRegion

section PadicExtensionValuation

variable {E : Type*} [NontriviallyNormedField E] [NormedAlgebra ℚ_[p] E]
  [IsUltrametricDist E] [Algebra ℤ_[p] E] [IsScalarTower ℤ_[p] ℚ_[p] E]

/-- An element of a finite-dimensional ultrametric extension of `Qp` which is
integral over `Zp` lies in the unit ball.

The unit ball is the integer ring of `NormedField.valuation`.  That integer ring
is integrally closed in the field, and `Zp` maps into it because the norm of a
`Qp`-scalar in a normed field extension is its `Qp`-norm. -/
theorem norm_le_one_of_isIntegral_padicExtension
    {x : E} (hx : IsIntegral ℤ_[p] x) : ‖x‖ ≤ 1 := by
  let v := NormedField.valuation (K := E)
  have hmem (z : ℤ_[p]) : algebraMap ℤ_[p] E z ∈ v.integer := by
    rw [Valuation.mem_integer_iff]
    change ‖algebraMap ℤ_[p] E z‖₊ ≤ 1
    rw [show algebraMap ℤ_[p] E z =
      algebraMap ℚ_[p] E (algebraMap ℤ_[p] ℚ_[p] z) from
        IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] E z]
    rw [← NNReal.coe_le_coe, coe_nnnorm, norm_algebraMap' E]
    exact z.property
  let f : ℤ_[p] →+* v.integer :=
    { toFun := fun z => ⟨algebraMap ℤ_[p] E z, hmem z⟩
      map_one' := Subtype.ext (map_one _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ _ _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  letI : Algebra ℤ_[p] v.integer := f.toAlgebra
  haveI : IsScalarTower ℤ_[p] v.integer E := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    rfl
  have hxint : IsIntegral v.integer x := IsIntegral.tower_top (A := v.integer) hx
  have hv : v.Integers v.integer := Valuation.integer.integers v
  have hvx : v x ≤ 1 := (Valuation.Integers.isIntegral_iff_v_le_one hv).mp hxint
  exact_mod_cast hvx

end PadicExtensionValuation

section CanonicalUnitReference

variable {J : Type (max u v)} [Finite J] {E : J → Type (max u v)}
  [∀ j, NontriviallyNormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
  [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
  [∀ j, IsUltrametricDist (E j)]

omit [Finite ι] in
/-- Integrality passes from the field-product unit region back to the actual
tuple tensor block along a genuine decomposition. -/
theorem isIntegral_of_mem_arithmeticTupleUnitReferencePullback
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j))
    {x : ArithmeticTensorTupleBlock places tuple}
    (hx : x ∈ arithmeticTupleUnitReferencePullback places tuple e) :
    IsIntegral ℤ_[p] x := by
  rw [arithmeticTupleUnitReferencePullback] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  letI : Algebra ℤ_[p] ((j : J) → E j) :=
    Algebra.restrictScalars ℤ_[p] ℚ_[p] ((j : J) → E j)
  haveI : IsScalarTower ℤ_[p] ℚ_[p] ((j : J) → E j) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hyint : IsIntegral ℤ_[p] y := isIntegral_of_mem_productUnitRegion hy
  have h := IsIntegral.map (e.symm.restrictScalars ℤ_[p]).toAlgHom hyint
  simpa only [AlgEquiv.coe_restrictScalars, AlgEquiv.toAlgHom_apply,
    AlgEquiv.symm_apply_apply] using h

end CanonicalUnitReference

/-- **The `O_hol` integrality interface.**  The actual canonical holomorphic
unit reference of a place-tuple tensor block is contained in the integral
closure of `Zp` in that block. -/
theorem arithmeticTupleCanonicalUnitReference_subset_integralClosure :
    (arithmeticTupleCanonicalUnitReference places tuple :
        Set (ArithmeticTensorTupleBlock places tuple)) ⊆
      (integralClosure ℤ_[p] (ArithmeticTensorTupleBlock places tuple) :
        Set (ArithmeticTensorTupleBlock places tuple)) := by
  letI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  letI : ∀ j, IsUltrametricDist (E j) := fun j => (hE j).2.2
  intro x hx
  rw [arithmeticTupleCanonicalUnitReference_eq places tuple e] at hx
  exact isIntegral_of_mem_arithmeticTupleUnitReferencePullback places tuple e hx

/-- Conversely, every element integral over `Zp` lies in the canonical
holomorphic unit reference: its decomposition coordinates are integral, hence
lie in the unit ball of their field factor. -/
theorem integralClosure_subset_arithmeticTupleCanonicalUnitReference :
    (integralClosure ℤ_[p] (ArithmeticTensorTupleBlock places tuple) :
        Set (ArithmeticTensorTupleBlock places tuple)) ⊆
      (arithmeticTupleCanonicalUnitReference places tuple :
        Set (ArithmeticTensorTupleBlock places tuple)) := by
  letI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  letI : ∀ j, IsUltrametricDist (E j) := fun j => (hE j).2.2
  intro x hx
  rw [arithmeticTupleCanonicalUnitReference_eq places tuple e,
    arithmeticTupleUnitReferencePullback]
  refine ⟨e x, ?_, e.symm_apply_apply x⟩
  intro j
  letI : Algebra ℤ_[p] (E j) := Algebra.restrictScalars ℤ_[p] ℚ_[p] (E j)
  have hcoord : IsIntegral ℤ_[p] ((e x) j) := by
    have h := IsIntegral.map (((Pi.evalAlgHom ℚ_[p] E j).comp e).restrictScalars ℤ_[p]) hx
    simpa only [AlgEquiv.toAlgHom_apply, AlgHom.restrictScalars_apply, AlgHom.comp_apply,
      Pi.evalAlgHom_apply] using h
  exact norm_le_one_of_isIntegral_padicExtension hcoord

/-- The canonical holomorphic unit reference is exactly the integral closure of
`Zp` in the actual tuple tensor block. -/
theorem arithmeticTupleCanonicalUnitReference_eq_integralClosure :
    (arithmeticTupleCanonicalUnitReference places tuple :
        Set (ArithmeticTensorTupleBlock places tuple)) =
      (integralClosure ℤ_[p] (ArithmeticTensorTupleBlock places tuple) :
        Set (ArithmeticTensorTupleBlock places tuple)) :=
  Set.Subset.antisymm
    (arithmeticTupleCanonicalUnitReference_subset_integralClosure places tuple)
    (integralClosure_subset_arithmeticTupleCanonicalUnitReference places tuple)

end

end LeanFormal.IUT.NumberFieldFinitePlace



