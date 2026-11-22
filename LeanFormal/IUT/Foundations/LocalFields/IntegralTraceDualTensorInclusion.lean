import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegerTensorComparison
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceHolomorphicIntegralClosure
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceLogShellScalingAssembly
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualLattice
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorFieldDecomposition
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellRamificationInertia
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# Trace-dual inclusion for the actual arithmetic tensor integer lattice

This file works with the actual finite tensor

`Q = ArithmeticTensorTupleBlock places tuple`

and its actual integral lattice

`R_I = arithmeticTupleValuationIntegerLattice places tuple`.

The first main construction is the genuine `Zp`-subalgebra of `Q` whose carrier is
exactly `R_I`.  The normalization `R_I~` is the actual integral closure of `Zp` in
the full tensor `Q`, not the integral closure inside `R_I`.  The trace-integrality
lemmas are ported from the temporary file
`tmp/prop11-tensor-normalization-20261017/TraceIntegral.lean`; no temporary file is
imported.

The final section proves that the resulting normalization is contained in the
integral trace dual of `R_I` with respect to `Algebra.traceForm Qp Q`.

This is an actual tensor-level trace-dual inclusion.  It is not a claim that the
full N4--N7 different/discriminant comparison has been closed.

## Handoff status (2026-10-18)

File: `D:\lean\LeanFormal\IUT\Foundations\LocalFields\IntegralTraceDualTensorInclusion.lean`.

Last attempted build: `trace-dual-paper-build15b.log`, guard exit 1, 3671/3671 jobs.
The sole error is at `padicInt_pow_mem_span_localDifferentGenerator`, line 684:
the rewrite chain after membership in the principal ideal still exposes
`∃ a, a • delta = p^m`, so `addVal_le_iff_dvd` cannot fire directly.

Last green build: `fix-trace-dual-tensor-local-build14.log`, guard exit 0, 3670 jobs.
Declarations proved green at that point include
`matrix_charpoly_root_isRoot_of_aeval_eq_zero`,
`matrix_trace_isIntegral_of_aeval`, `algebra_trace_isIntegral`,
`piTensorProduct_trace_tprod`,
`basisIntegralLattice_padicBasisOfIntegralBasis`,
`padicIntegralTraceDualLattice_basisIntegralLattice_eq_basisIntegralLattice`,
`arithmeticTupleValuationIntegerLattice_eq_basisIntegralLattice`,
`arithmeticTupleValuationIntegerLattice_le_normalization`,
`arithmeticTupleValuationIntegerNormalization_le_traceDual`,
`localDifferentGenerator_mem`,
`localDifferentGenerator_mul_mem_integralTraceDual`,
`arithmeticTupleValuationIntegerTraceDual_eq_basisIntegralLattice`,
`arithmeticTupleLocalTraceDual_eq_basisIntegralLattice`,
`arithmeticTensorDifferentGenerator_mul_mem_traceDual`,
`arithmeticTensorDifferentGenerator_mul_mem_arithmeticTupleValuationIntegerLattice`, and
`arithmeticTensorDifferentGenerator_mul_mem_of_mem_arithmeticTupleCanonicalUnitReference`.

The current source additionally contains, but has not reached a green build:
`localDifferentGenerator_span_eq`, `localDifferentGenerator_ne_zero`,
`localDifferentOrder`, `localDifferentPaperOrder`,
`padicInt_pow_mem_span_localDifferentGenerator`,
`arithmeticTensorDifferentGeneratorMulSubmodule`,
`arithmeticTupleValuationIntegerNormalization_toSubmodule_eq_canonicalUnitReference`,
and `arithmeticTensorPaperDifferentScale` (conditional on the explicit `hdiff`
order-to-scalar bridge).

Next precise action: repair line 684 by converting principal-ideal membership
through the divisibility form (`Ideal.mem_span_singleton`, not the `exists smul`
variant), apply `IsDiscreteValuationRing.addVal_le_iff_dvd`, then close the
remaining order inequality with `hpm`; rerun guard and the formal axiom probe.
-/

namespace LeanFormal.IUT.IntegralTraceDualTensorInclusion

open Polynomial Module
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IntegralTraceDual
open LeanFormal.IUT.FinitePadicIntegralLattice
open scoped LeanFormal.IUT.FinitePadicIntegralLattice
open scoped TensorProduct

set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

noncomputable section

universe u v w

/-! ## Trace integrality over a commutative base ring -/

/-- A root of the characteristic polynomial of a matrix over a field is a root of every
polynomial annihilating the matrix. -/
theorem matrix_charpoly_root_isRoot_of_aeval_eq_zero {Ω : Type*} [Field Ω] {n : Type*}
    [Fintype n] [DecidableEq n] (M : Matrix n n Ω) (p : Polynomial Ω) (hp : aeval M p = 0) {μ : Ω}
    (hμ : M.charpoly.IsRoot μ) : p.IsRoot μ := by
  let f : Module.End Ω (n → Ω) := Matrix.toLin' M
  have hf : f.charpoly = M.charpoly := Matrix.charpoly_toLin' M
  have heig : f.HasEigenvalue μ := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hf]
    exact hμ
  have hmin : (minpoly Ω f).IsRoot μ := Module.End.isRoot_of_hasEigenvalue heig
  have hfp : aeval f p = 0 := by
    have : aeval f p = Matrix.toLinAlgEquiv' (aeval M p) := by
      exact Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' : Matrix n n Ω ≃ₐ[Ω] _) M p
    rw [this, hp, map_zero]
  exact Polynomial.IsRoot.dvd hmin (minpoly.dvd Ω f hfp)

/-- If a matrix over a field `F` is annihilated by (the image of) a monic polynomial over `C`,
its trace is integral over `C`. -/
theorem matrix_trace_isIntegral_of_aeval {C F : Type*} [CommRing C] [Field F] [Algebra C F]
    {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n F) (g : Polynomial C) (hg : g.Monic)
    (hM : aeval M (g.map (algebraMap C F)) = 0) : IsIntegral C M.trace := by
  let Ω := AlgebraicClosure F
  let φ : F →+* Ω := algebraMap F Ω
  let M' : Matrix n n Ω := M.map φ
  have hsplit : M'.charpoly.Splits := IsAlgClosed.splits _
  have htrace : φ M.trace = M'.trace := by
    simp [M', Matrix.trace, Matrix.map_apply, map_sum]
  have hM' : aeval M' (g.map (algebraMap C Ω)) = 0 := by
    have h1 : g.map (algebraMap C Ω) = (g.map (algebraMap C F)).map φ := by
      rw [Polynomial.map_map]; congr 1
    have h2 : aeval M' ((g.map (algebraMap C F)).map φ) =
        (aeval M (g.map (algebraMap C F))).map φ := by
      rw [show φ = algebraMap F Ω from rfl, Polynomial.aeval_map_algebraMap]
      exact Polynomial.aeval_algHom_apply ((Algebra.ofId F Ω).mapMatrix) M _
    rw [h1, h2, hM, Matrix.map_zero _ (map_zero φ)]
  rw [← isIntegral_algebraMap_iff φ.injective, show (algebraMap F Ω) M.trace = φ M.trace from rfl,
    htrace, Matrix.trace_eq_sum_roots_charpoly_of_splits hsplit]
  refine IsIntegral.multiset_sum fun μ hμ => ?_
  have hroot : M'.charpoly.IsRoot μ :=
    (Polynomial.mem_roots (Matrix.charpoly_monic M').ne_zero).mp hμ
  have := matrix_charpoly_root_isRoot_of_aeval_eq_zero M' _ hM' hroot
  refine ⟨g, hg, ?_⟩
  rw [Polynomial.IsRoot, Polynomial.eval_map] at this
  exact this

/-- **Trace of an integral element of a finite algebra over a field.** If `w` in a finite
`F`-algebra `Q` is integral over `C` (with `C → F → Q`), then `Tr_{Q/F}(w)` is integral over
`C`.  Mathlib's `Algebra.isIntegral_trace` requires `Q` to be a field, so we port the
finite-algebra argument used for the tensor normalization. -/
theorem algebra_trace_isIntegral {C F Q : Type*} [CommRing C] [Field F] [CommRing Q]
    [Algebra F Q] [Module.Finite F Q] [Algebra C F] [Algebra C Q] [IsScalarTower C F Q]
    {w : Q} (hw : IsIntegral C w) : IsIntegral C (Algebra.trace F Q w) := by
  classical
  obtain ⟨g, hg, hgw⟩ := hw
  let b := Module.Free.chooseBasis F Q
  rw [Algebra.trace_eq_matrix_trace b]
  refine matrix_trace_isIntegral_of_aeval _ g hg ?_
  have : aeval w (g.map (algebraMap C F)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap, aeval_def]
    exact hgw
  rw [Polynomial.aeval_algHom_apply (Algebra.leftMulMatrix b), this, map_zero]

/-- The trace of an elementary tensor is the product of the traces of its factors. -/
theorem piTensorProduct_trace_tprod {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)] (y : ∀ i, A i) :
    Algebra.trace R (⨂[R] i, A i) (PiTensorProduct.tprod R y) =
      ∏ i, Algebra.trace R (A i) (y i) := by
  classical
  let b := fun i => Module.Free.chooseBasis R (A i)
  rw [Algebra.trace_eq_matrix_trace (Basis.piTensorProduct b)]
  simp_rw [fun i => Algebra.trace_eq_matrix_trace (b i) (y i)]
  simp only [Matrix.trace, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Basis.piTensorProduct_apply, PiTensorProduct.tprod_mul_tprod,
    Basis.piTensorProduct_repr_tprod_apply]
  rfl

section TraceDualBasis

variable {p : ℕ} [Fact p.Prime] {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℚ_[p] Q]
  [FiniteDimensional ℚ_[p] Q] {κ : Type*} [Fintype κ]

/-- The integral lattice spanned by the rational basis obtained from an integral
basis recovers the original integral lattice. -/
theorem basisIntegralLattice_padicBasisOfIntegralBasis
    (S : Submodule ℤ_[p] Q) (basis : Module.Basis κ ℤ_[p] S)
    (hspan : Submodule.span ℚ_[p] (S : Set Q) = ⊤) :
    basisIntegralLattice (padicBasisOfIntegralBasis S basis hspan) = S := by
  rw [basisIntegralLattice]
  have hrange : Set.range (padicBasisOfIntegralBasis S basis hspan) =
      Set.range (fun j => (basis j : Q)) := by
    apply congrArg Set.range
    funext j
    exact padicBasisOfIntegralBasis_apply S basis hspan j
  rw [hrange]
  change Submodule.span ℤ_[p] (Set.range (S.subtype ∘ basis)) = S
  rw [Set.range_comp, ← Submodule.map_span, basis.span_eq]
  simp

/-- If `c` is a basis dual to `b` for a bilinear form, then the integral trace
dual of the lattice spanned by `b` is the lattice spanned by `c`. -/
theorem padicIntegralTraceDualLattice_basisIntegralLattice_eq_basisIntegralLattice
    [DecidableEq κ] (B : LinearMap.BilinForm ℚ_[p] Q) (b c : Module.Basis κ ℚ_[p] Q)
    (h : ∀ j k, B (c k) (b j) = if k = j then (1 : ℚ_[p]) else 0) :
    padicIntegralTraceDualLattice B (basisIntegralLattice b) =
      basisIntegralLattice c := by
  classical
  apply le_antisymm
  · intro x hx
    rw [← c.sum_repr x]
    apply Submodule.sum_mem
    intro j _
    have hcoeff : B x (b j) = c.repr x j := by
      conv_lhs => rw [← c.sum_repr x]
      change (B.flip (b j)) (∑ k, c.repr x k • c k) = c.repr x j
      rw [map_sum]
      simp only [map_smul]
      rw [Finset.sum_eq_single j]
      · rw [LinearMap.BilinForm.flip_apply, h j j]
        simp
      · intro k _ hk
        rw [LinearMap.BilinForm.flip_apply, h j k]
        simp [hk]
      · intro hj
        simp at hj
    have hmem : c.repr x j ∈ (1 : Submodule ℤ_[p] ℚ_[p]) := by
      rw [← hcoeff]
      exact hx (b j) (Submodule.subset_span ⟨j, rfl⟩)
    obtain ⟨z, hz⟩ := Submodule.mem_one.mp hmem
    have hterm := (basisIntegralLattice c).smul_mem z
      (Submodule.subset_span ⟨j, rfl⟩)
    have hzcoe : (z : ℚ_[p]) = c.repr x j := hz
    simpa only [padicInteger_smul_eq, hzcoe] using hterm
  · rw [show basisIntegralLattice c = Submodule.span ℤ_[p] (Set.range c) from rfl,
      Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    change c k ∈ padicIntegralTraceDualLattice B (basisIntegralLattice b)
    rw [mem_padicIntegralTraceDualLattice_iff]
    intro y hy
    let T : Submodule ℤ_[p] Q :=
      Submodule.comap ((B (c k)).restrictScalars ℤ_[p])
        (1 : Submodule ℤ_[p] ℚ_[p])
    have hgen : Set.range b ⊆ (T : Set Q) := by
      rintro _ ⟨j, rfl⟩
      change B (c k) (b j) ∈ (1 : Submodule ℤ_[p] ℚ_[p])
      rw [h j k]
      by_cases hkj : k = j
      · subst hkj
        simpa using
          (Submodule.one_le (P := (1 : Submodule ℤ_[p] ℚ_[p]))).mp le_rfl
      · simp [hkj]
    have hle : basisIntegralLattice b ≤ T := by
      rw [show basisIntegralLattice b = Submodule.span ℤ_[p] (Set.range b) from rfl]
      exact Submodule.span_le.mpr hgen
    exact hle hy

end TraceDualBasis
/-! ## The actual tensor lattice as a `Zp`-subalgebra -/

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

/-- The chosen `Zp`-algebra structure on the actual tensor coming from the scalar tower
`Zp → Qp → Q`. -/
local instance arithmeticTensorTupleZpAlgebra :
    Algebra ℤ_[p] (ArithmeticTensorTupleBlock places tuple) :=
  Algebra.restrictScalars ℤ_[p] ℚ_[p] (ArithmeticTensorTupleBlock places tuple)

/-- The actual pure integral tensor region generating `R_I`. -/
abbrev arithmeticTupleValuationIntegerRegion :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  tensorIntegralRegion (p := p)
    (M := fun i => CommonPrimeCompletion (places i (tuple i)))
    (fun i => (valuationIntegerLattice
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p) :
        Set (CommonPrimeCompletion (places i (tuple i)))))

/-- `R_I` is definitionally the `Zp`-span of the actual pure integral tensor region. -/
theorem arithmeticTupleValuationIntegerLattice_eq_span :
    arithmeticTupleValuationIntegerLattice places tuple =
      Submodule.span ℤ_[p] (arithmeticTupleValuationIntegerRegion places tuple) := rfl

/-- The rational basis of the tensor obtained by tensoring chosen integral bases of the
local valuation lattices. -/
noncomputable def arithmeticTupleValuationIntegerQpBasis :
    Module.Basis
      ((i : ι) → Module.Free.ChooseBasisIndex ℤ_[p]
        (valuationIntegerLattice (K := CommonPrimeCompletion (places i (tuple i))) (p := p)))
      ℚ_[p] (⨂[ℚ_[p]] i, CommonPrimeCompletion (places i (tuple i))) :=
  submoduleTensorPadicBasis (p := p)
    (M := fun i => CommonPrimeCompletion (places i (tuple i)))
    (S := fun i => valuationIntegerLattice
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p))
    (fun i => span_padic_valuationIntegerLattice_eq_top
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p))

/-- The local completed field at one tuple coordinate. -/
abbrev arithmeticTupleLocalField (i : ι) :=
  CommonPrimeCompletion (places i (tuple i))

/-- The local valuation integer lattice at one tuple coordinate. -/
abbrev arithmeticTupleLocalIntegerLattice (i : ι) :
    Submodule ℤ_[p] (arithmeticTupleLocalField places tuple i) :=
  valuationIntegerLattice (K := arithmeticTupleLocalField places tuple i) (p := p)

/-- The index type of the chosen local integral basis. -/
abbrev arithmeticTupleLocalBasisIndex (i : ι) :=
  Module.Free.ChooseBasisIndex ℤ_[p] (arithmeticTupleLocalIntegerLattice places tuple i)

/-- The chosen rational basis of a local field, extending its integral basis. -/
noncomputable def arithmeticTupleLocalQpBasis (i : ι) :
    Module.Basis (arithmeticTupleLocalBasisIndex places tuple i) ℚ_[p]
      (arithmeticTupleLocalField places tuple i) :=
  padicBasisOfIntegralBasis (arithmeticTupleLocalIntegerLattice places tuple i)
    (Module.Free.chooseBasis ℤ_[p] (arithmeticTupleLocalIntegerLattice places tuple i))
    (span_padic_valuationIntegerLattice_eq_top
      (K := arithmeticTupleLocalField places tuple i) (p := p))

/-- The tensor basis is exactly the tensor product of the local rational bases. -/
theorem arithmeticTupleValuationIntegerQpBasis_eq_piTensorProduct :
    arithmeticTupleValuationIntegerQpBasis places tuple =
      Basis.piTensorProduct (arithmeticTupleLocalQpBasis places tuple) := rfl

/-- The local trace form is nondegenerate. -/
theorem arithmeticTupleLocalTraceForm_nondegenerate (i : ι) :
    (Algebra.traceForm ℚ_[p] (arithmeticTupleLocalField places tuple i)).Nondegenerate :=
  traceForm_nondegenerate ℚ_[p] _

/-- The local trace-dual basis. -/
noncomputable def arithmeticTupleLocalDualQpBasis (i : ι) :
    Module.Basis (arithmeticTupleLocalBasisIndex places tuple i) ℚ_[p]
      (arithmeticTupleLocalField places tuple i) :=
  (Algebra.traceForm ℚ_[p] (arithmeticTupleLocalField places tuple i)).dualBasis
    (arithmeticTupleLocalTraceForm_nondegenerate places tuple i)
    (arithmeticTupleLocalQpBasis places tuple i)

/-- The actual tensor trace-dual basis, the tensor product of the local dual bases. -/
noncomputable def arithmeticTupleValuationIntegerDualQpBasis :
    Module.Basis ((i : ι) → arithmeticTupleLocalBasisIndex places tuple i) ℚ_[p]
      (ArithmeticTensorTupleBlock places tuple) :=
  Basis.piTensorProduct (arithmeticTupleLocalDualQpBasis places tuple)
/-- The actual tensor integer lattice is exactly the `Zp`-span of the pure tensor basis
coming from chosen integral bases of the local valuation lattices. -/
theorem arithmeticTupleValuationIntegerLattice_eq_basisIntegralLattice :
    arithmeticTupleValuationIntegerLattice places tuple =
      basisIntegralLattice (arithmeticTupleValuationIntegerQpBasis places tuple) := by
  classical
  let S : (i : ι) → Submodule ℤ_[p] (CommonPrimeCompletion (places i (tuple i))) :=
    fun i => valuationIntegerLattice (K := CommonPrimeCompletion (places i (tuple i))) (p := p)
  let hspan : ∀ i,
      Submodule.span ℚ_[p] (S i : Set (CommonPrimeCompletion (places i (tuple i)))) = ⊤ :=
    fun i => span_padic_valuationIntegerLattice_eq_top
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p)
  let f := submoduleTensorMap (p := p)
    (M := fun i => CommonPrimeCompletion (places i (tuple i))) S
  let bint : Module.Basis
      ((i : ι) → Module.Free.ChooseBasisIndex ℤ_[p] (S i)) ℤ_[p]
      (⨂[ℤ_[p]] i, S i) :=
    Basis.piTensorProduct fun i => Module.Free.chooseBasis ℤ_[p] (S i)
  let b : Module.Basis
      ((i : ι) → Module.Free.ChooseBasisIndex ℤ_[p] (S i)) ℚ_[p]
      (⨂[ℚ_[p]] i, CommonPrimeCompletion (places i (tuple i))) :=
    submoduleTensorPadicBasis (p := p) (M := fun i => CommonPrimeCompletion (places i (tuple i)))
      S hspan
  have hb : ∀ j, f (bint j) = b j := by
    intro j
    simp only [f, bint, Basis.piTensorProduct_apply, submoduleTensorMap_tprod]
    change PiTensorProduct.tprod ℚ_[p] _ = (Basis.piTensorProduct _) j
    rw [Basis.piTensorProduct_apply]
    congr 1
    funext i
    exact (padicBasisOfIntegralBasis_apply (S i) (Module.Free.chooseBasis ℤ_[p] (S i))
      (hspan i) (j i)).symm
  have hspan : (arithmeticTupleValuationIntegerLattice places tuple :
      Submodule ℤ_[p] (⨂[ℚ_[p]] i, CommonPrimeCompletion (places i (tuple i)))) =
      Submodule.span ℤ_[p] (Set.range b) := by
    calc
      (arithmeticTupleValuationIntegerLattice places tuple :
          Submodule ℤ_[p] (⨂[ℚ_[p]] i, CommonPrimeCompletion (places i (tuple i)))) =
          Submodule.map f (⊤ : Submodule ℤ_[p] (⨂[ℤ_[p]] i, S i)) := by
        rw [Submodule.map_top, range_submoduleTensorMap]
        rfl
      _ = Submodule.map f (Submodule.span ℤ_[p] (Set.range bint)) := by rw [bint.span_eq]
      _ = Submodule.span ℤ_[p] (f '' Set.range bint) := by rw [Submodule.map_span]
      _ = Submodule.span ℤ_[p] (Set.range b) := by
        rw [← Set.range_comp]
        rw [show Set.range (⇑f ∘ ⇑bint) = Set.range (⇑b) by
          apply congrArg Set.range
          funext j
          exact hb j]
        rfl
  change (arithmeticTupleValuationIntegerLattice places tuple :
      Submodule ℤ_[p] (⨂[ℚ_[p]] i, CommonPrimeCompletion (places i (tuple i)))) =
    basisIntegralLattice (arithmeticTupleValuationIntegerQpBasis places tuple)
  rw [hspan]
  change Submodule.span ℤ_[p] (Set.range b) =
    Submodule.span ℤ_[p] (Set.range (arithmeticTupleValuationIntegerQpBasis places tuple))
  rfl

/-- The tensor identity belongs to the actual pure integral region. -/
theorem one_mem_arithmeticTupleValuationIntegerRegion :
    (1 : ArithmeticTensorTupleBlock places tuple) ∈
      arithmeticTupleValuationIntegerRegion places tuple := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro i _
    exact (Integers (CommonPrimeCompletion (places i (tuple i)))).one_mem
  · exact (PiTensorProduct.one_def).symm

/-- The actual pure integral region is closed under multiplication. -/
theorem mul_mem_arithmeticTupleValuationIntegerRegion
    {x y : ArithmeticTensorTupleBlock places tuple}
    (hx : x ∈ arithmeticTupleValuationIntegerRegion places tuple)
    (hy : y ∈ arithmeticTupleValuationIntegerRegion places tuple) :
    x * y ∈ arithmeticTupleValuationIntegerRegion places tuple := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  refine ⟨fun i => a i * b i, ?_, ?_⟩
  · intro i _
    exact (Integers (CommonPrimeCompletion (places i (tuple i)))).mul_mem
      (ha i (Set.mem_univ i)) (hb i (Set.mem_univ i))
  · change PiTensorProduct.tprod ℚ_[p] (fun i => a i * b i) =
      PiTensorProduct.tprod ℚ_[p] a * PiTensorProduct.tprod ℚ_[p] b
    exact (PiTensorProduct.tprod_mul_tprod a b).symm

/-- The actual lattice contains the tensor identity. -/
theorem one_mem_arithmeticTupleValuationIntegerLattice :
    (1 : ArithmeticTensorTupleBlock places tuple) ∈
      arithmeticTupleValuationIntegerLattice places tuple := by
  rw [arithmeticTupleValuationIntegerLattice_eq_span]
  exact Submodule.subset_span (one_mem_arithmeticTupleValuationIntegerRegion places tuple)

/-- The actual lattice is closed under multiplication. -/
theorem mul_mem_arithmeticTupleValuationIntegerLattice
    {x y : ArithmeticTensorTupleBlock places tuple}
    (hx : x ∈ arithmeticTupleValuationIntegerLattice places tuple)
    (hy : y ∈ arithmeticTupleValuationIntegerLattice places tuple) :
    x * y ∈ arithmeticTupleValuationIntegerLattice places tuple := by
  have hxy : x * y ∈
      Submodule.span ℤ_[p] (arithmeticTupleValuationIntegerRegion places tuple) *
        Submodule.span ℤ_[p] (arithmeticTupleValuationIntegerRegion places tuple) :=
    Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at hxy
  rw [arithmeticTupleValuationIntegerLattice_eq_span]
  exact Submodule.span_mono (by
    intro z hz
    rcases hz with ⟨a, ha, b, hb, rfl⟩
    exact mul_mem_arithmeticTupleValuationIntegerRegion places tuple ha hb) hxy

/-- The actual integer lattice as a genuine `Zp`-subalgebra of the tensor. -/
def arithmeticTupleValuationIntegerSubalgebra :
    Subalgebra ℤ_[p] (ArithmeticTensorTupleBlock places tuple) where
  carrier := (arithmeticTupleValuationIntegerLattice places tuple :
    Set (ArithmeticTensorTupleBlock places tuple))
  add_mem' := fun hx hy =>
    (arithmeticTupleValuationIntegerLattice places tuple).add_mem hx hy
  zero_mem' := (arithmeticTupleValuationIntegerLattice places tuple).zero_mem
  mul_mem' := fun hx hy =>
    mul_mem_arithmeticTupleValuationIntegerLattice places tuple hx hy
  one_mem' := one_mem_arithmeticTupleValuationIntegerLattice places tuple
  algebraMap_mem' := fun r => by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (arithmeticTupleValuationIntegerLattice places tuple).smul_mem r
      (one_mem_arithmeticTupleValuationIntegerLattice places tuple)

/-- The carrier of the constructed subalgebra is exactly `R_I`. -/
theorem arithmeticTupleValuationIntegerSubalgebra_coe :
    (arithmeticTupleValuationIntegerSubalgebra places tuple :
      Set (ArithmeticTensorTupleBlock places tuple)) =
        (arithmeticTupleValuationIntegerLattice places tuple :
          Set (ArithmeticTensorTupleBlock places tuple)) := rfl

/-! ## Integrality of actual lattice elements -/

/-- The actual integer lattice is finite over `Zp`, hence every element of its
subalgebra is integral over `Zp`. -/
theorem isIntegral_arithmeticTupleValuationIntegerSubalgebra
    (x : arithmeticTupleValuationIntegerSubalgebra places tuple) :
    IsIntegral ℤ_[p] x := by
  haveI : Module.Finite ℤ_[p] (arithmeticTupleValuationIntegerSubalgebra places tuple) :=
    inferInstanceAs (Module.Finite ℤ_[p]
      (arithmeticTupleValuationIntegerLattice places tuple))
  exact IsIntegral.of_finite ℤ_[p] x

/-- The actual normalization `R_I~` of the tensor integer lattice: the integral
closure of `Zp` in the full tensor `Q`. -/
abbrev arithmeticTupleValuationIntegerNormalization :
    Subalgebra ℤ_[p] (ArithmeticTensorTupleBlock places tuple) :=
  integralClosure ℤ_[p] (ArithmeticTensorTupleBlock places tuple)

/-- Every element of `R_I~` is integral over `Zp`. -/
theorem isIntegral_arithmeticTupleValuationIntegerNormalization
    {z : ArithmeticTensorTupleBlock places tuple}
    (hz : z ∈ arithmeticTupleValuationIntegerNormalization places tuple) :
    IsIntegral ℤ_[p] z := by
  exact hz

/-- Every element of the actual tensor integer lattice is integral over `Zp`. -/
theorem isIntegral_arithmeticTupleValuationIntegerLattice
    {r : ArithmeticTensorTupleBlock places tuple}
    (hr : r ∈ arithmeticTupleValuationIntegerLattice places tuple) :
    IsIntegral ℤ_[p] r := by
  exact IsIntegral.map (arithmeticTupleValuationIntegerSubalgebra places tuple).val
    (isIntegral_arithmeticTupleValuationIntegerSubalgebra places tuple ⟨r, hr⟩)

/-- The actual tensor integer lattice is contained in its normalization in `Q`. -/
theorem arithmeticTupleValuationIntegerLattice_le_normalization :
    (arithmeticTupleValuationIntegerLattice places tuple) ≤
      (arithmeticTupleValuationIntegerNormalization places tuple).toSubmodule := by
  intro r hr
  change IsIntegral ℤ_[p] r
  exact isIntegral_arithmeticTupleValuationIntegerLattice places tuple hr

/-- `Zp` is integrally closed in `Qp`. -/
theorem padicInt_isIntegrallyClosed : IsIntegrallyClosed ℤ_[p] := by
  have hnot : ¬ IsField ℤ_[p] := IsDiscreteValuationRing.not_isField ℤ_[p]
  have hTFAE := IsDiscreteValuationRing.TFAE ℤ_[p] hnot
  have h03 : IsDiscreteValuationRing ℤ_[p] ↔
      (IsIntegrallyClosed ℤ_[p] ∧
        ∃! P : Ideal ℤ_[p], P ≠ ⊥ ∧ P.IsPrime) :=
    hTFAE.out 0 3
  exact (h03.mp (inferInstance : IsDiscreteValuationRing ℤ_[p])).1

/-- An element of `Qp` integral over `Zp` lies in the unit submodule `Zp`. -/
theorem padicInt_mem_one_of_isIntegral {x : ℚ_[p]} (hx : IsIntegral ℤ_[p] x) :
    x ∈ (1 : Submodule ℤ_[p] ℚ_[p]) := by
  haveI : IsIntegrallyClosed ℤ_[p] := padicInt_isIntegrallyClosed (p := p)
  exact Submodule.mem_one.mpr
    ((IsIntegrallyClosed.isIntegral_iff (R := ℤ_[p]) (K := ℚ_[p])).mp hx)

/-- The actual normalization `R_I~` is contained in the integral trace dual of `R_I`
for the multiplicative trace form `Tr_{Q/Qp}(x * y)`. -/
theorem arithmeticTupleValuationIntegerNormalization_le_traceDual :
    (arithmeticTupleValuationIntegerNormalization places tuple).toSubmodule ≤
      padicIntegralTraceDualLattice
        (Algebra.traceForm ℚ_[p] (ArithmeticTensorTupleBlock places tuple))
        (arithmeticTupleValuationIntegerLattice places tuple) := by
  intro z hz
  rw [mem_padicIntegralTraceDualLattice_iff]
  intro r hr
  let Q := ArithmeticTensorTupleBlock places tuple
  have hzint : IsIntegral ℤ_[p] z :=
    isIntegral_arithmeticTupleValuationIntegerNormalization places tuple hz
  have hrint : IsIntegral ℤ_[p] r :=
    isIntegral_arithmeticTupleValuationIntegerLattice places tuple hr
  have htrace : IsIntegral ℤ_[p] (Algebra.trace ℚ_[p] Q (z * r)) :=
    algebra_trace_isIntegral (C := ℤ_[p]) (F := ℚ_[p]) (Q := Q)
      (w := z * r) (IsIntegral.mul hzint hrint)
  rw [Algebra.traceForm_apply]
  exact padicInt_mem_one_of_isIntegral (p := p) htrace

/-! ## The local different ideal at a completed finite place -/

section LocalDifferent

variable {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L]
  [IsUltrametricDist L] [ProperSpace L] [NormedAlgebra ℚ_[p] L]
  [FiniteDimensional ℚ_[p] L]

/-- The `Zp`-algebra map into the norm-integer ring of a `Qp`-normed field. -/
noncomputable def padicIntToIntegers : ℤ_[p] →+* Integers L :=
  RingHom.codRestrict ((algebraMap ℚ_[p] L).comp (algebraMap ℤ_[p] ℚ_[p])) (Integers L)
    (fun z => by
      change ‖algebraMap ℚ_[p] L (z : ℚ_[p])‖ ≤ 1
      rw [norm_algebraMap']
      exact z.property)

/-- The canonical `Zp`-algebra structure on the norm-integer ring. -/
instance integersZpAlgebra : Algebra ℤ_[p] (Integers L) :=
  padicIntToIntegers.toAlgebra

/-- The `Zp`-algebra structure on the local field, restricted from `Qp`. -/
instance localFieldZpAlgebra : Algebra ℤ_[p] L :=
  Algebra.restrictScalars ℤ_[p] ℚ_[p] L

instance integersScalarTower : IsScalarTower ℤ_[p] (Integers L) L :=
  IsScalarTower.of_algebraMap_eq (R := ℤ_[p]) (S := Integers L) (A := L) fun _ => rfl

include p in
/-- The norm-integer ring of a finite extension of `Qp` is a discrete valuation ring.
This reuses the existing properness argument instead of constructing a new instance. -/
theorem integersIsDiscreteValuationRing : IsDiscreteValuationRing (Integers L) :=
  isDiscreteValuationRingIntegers (K := L) (p := p)

include p in
theorem integersIsIntegrallyClosed : IsIntegrallyClosed (Integers L) :=
  inferInstance

include p in
theorem integersIsDedekindDomain : IsDedekindDomain (Integers L) := by
  haveI : IsDiscreteValuationRing (Integers L) :=
    integersIsDiscreteValuationRing (p := p) (L := L)
  exact inferInstance

/-- The identity linear equivalence between the norm-integer ring and the actual
valuation integer lattice. -/
noncomputable def integersEquivValuationIntegerLattice :
    (Integers L) ≃ₗ[ℤ_[p]] (valuationIntegerLattice (K := L) (p := p)) where
  toFun x := ⟨x, x.property⟩
  invFun x := ⟨x, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' z x := by
    apply Subtype.ext
    change ((padicIntToIntegers (p := p) z : Integers L) : L) * (x : L) =
      (z : ℚ_[p]) • (x : L)
    rw [Algebra.smul_def]
    rfl

instance integersModuleFinite : Module.Finite ℤ_[p] (Integers L) :=
  Module.Finite.of_surjective
    (integersEquivValuationIntegerLattice (p := p) (L := L)).symm.toLinearMap
    (LinearEquiv.surjective _)

instance integersIsIntegralClosure : IsIntegralClosure (Integers L) ℤ_[p] L := by
  haveI : IsFractionRing (Integers L) L := inferInstance
  haveI : IsIntegrallyClosed (Integers L) := integersIsIntegrallyClosed (p := p) (L := L)
  exact inferInstance

instance integersIsTorsionFree : Module.IsTorsionFree ℤ_[p] (Integers L) :=
  Module.IsTorsionFree.of_smul_eq_zero fun z x hz => by
    have hcoe : (z : ℚ_[p]) • (x : L) = 0 := by
      have h := congrArg (fun y : Integers L => (y : L)) hz
      rw [Algebra.smul_def, Subring.coe_mul, Subring.coe_zero] at h
      change (algebraMap ℚ_[p] L (z : ℚ_[p])) * (x : L) = 0 at h
      rwa [Algebra.smul_def]
    rcases smul_eq_zero.mp hcoe with hz0 | hx0
    · left
      exact Subtype.ext hz0
    · right
      exact Subtype.ext hx0

include p in
/-- The local different ideal of `Integers L` over `Zp`. -/
noncomputable def localDifferentIdeal : Ideal (Integers L) := by
  haveI : IsIntegrallyClosed ℤ_[p] := padicInt_isIntegrallyClosed (p := p)
  haveI : IsDedekindDomain (Integers L) := integersIsDedekindDomain (p := p) (L := L)
  haveI : Module.IsTorsionFree ℤ_[p] (Integers L) := integersIsTorsionFree (p := p) (L := L)
  exact differentIdeal ℤ_[p] (Integers L)

include p in
/-- A generator of the local different ideal.  The integer ring is a discrete
valuation ring, so this ideal is principal. -/
noncomputable def localDifferentGenerator : Integers L := by
  haveI : IsDiscreteValuationRing (Integers L) :=
    integersIsDiscreteValuationRing (p := p) (L := L)
  exact Submodule.IsPrincipal.generator (localDifferentIdeal (p := p) (L := L))

include p in
theorem localDifferentGenerator_mem :
    localDifferentGenerator (p := p) (L := L) ∈
      localDifferentIdeal (p := p) (L := L) := by
  haveI : IsDiscreteValuationRing (Integers L) :=
    integersIsDiscreteValuationRing (p := p) (L := L)
  exact Submodule.IsPrincipal.generator_mem (localDifferentIdeal (p := p) (L := L))

include p in
/-- The chosen local different generator spans the actual local different ideal. -/
theorem localDifferentGenerator_span_eq :
    Ideal.span {localDifferentGenerator (p := p) (L := L)} =
      localDifferentIdeal (p := p) (L := L) := by
  haveI : IsDiscreteValuationRing (Integers L) :=
    integersIsDiscreteValuationRing (p := p) (L := L)
  exact Submodule.IsPrincipal.span_singleton_generator
    (localDifferentIdeal (p := p) (L := L))

include p in
/-- The local different generator is nonzero because the different ideal is nonzero. -/
theorem localDifferentGenerator_ne_zero :
    localDifferentGenerator (p := p) (L := L) ≠ 0 := by
  intro hzero
  haveI : IsIntegrallyClosed ℤ_[p] := padicInt_isIntegrallyClosed (p := p)
  haveI : IsDedekindDomain (Integers L) := integersIsDedekindDomain (p := p) (L := L)
  haveI : Module.IsTorsionFree ℤ_[p] (Integers L) := integersIsTorsionFree (p := p) (L := L)
  haveI : IsIntegralClosure (Integers L) ℤ_[p] L := integersIsIntegralClosure (p := p) (L := L)
  have hbot : localDifferentIdeal (p := p) (L := L) = ⊥ := by
    rw [← localDifferentGenerator_span_eq (p := p) (L := L)]
    simp [hzero]
  exact differentIdeal_ne_bot (A := ℤ_[p]) (B := Integers L) hbot

include p in
/-- The additive DVR order of the chosen local different generator.  This is the
order in uniformizer units; the paper's order normalized by `ord(p) = 1` is
`localDifferentPaperOrder` below. -/
noncomputable def localDifferentOrder : ℕ := by
  haveI : IsDiscreteValuationRing (Integers L) :=
    integersIsDiscreteValuationRing (p := p) (L := L)
  exact (IsDiscreteValuationRing.addVal (Integers L)
    (localDifferentGenerator (p := p) (L := L))).toNat

include p in
/-- The paper-normalized order `d = ord(different generator)`, with `ord(p) = 1`. -/
noncomputable def localDifferentPaperOrder : ℝ :=
  (localDifferentOrder (p := p) (L := L) : ℝ) /
    (logShellRamificationExponent (K := L) (p := p) : ℝ)

include p in
/-- If the paper-normalized different order is at most `m`, then `p^m` lies in
the principal ideal generated by the local different generator. -/
theorem padicInt_pow_mem_span_localDifferentGenerator
    (m : ℕ)
    (hm : localDifferentPaperOrder (p := p) (L := L) ≤ (m : ℝ)) :
    (p : Integers L) ^ m ∈
      Ideal.span {localDifferentGenerator (p := p) (L := L)} := by
  haveI hDVR : IsDiscreteValuationRing (Integers L) :=
    integersIsDiscreteValuationRing (p := p) (L := L)
  have hδne : localDifferentGenerator (p := p) (L := L) ≠ 0 :=
    localDifferentGenerator_ne_zero (p := p) (L := L)
  have hfin : IsDiscreteValuationRing.addVal (Integers L)
      (localDifferentGenerator (p := p) (L := L)) ≠ ⊤ := by
    exact fun htop => hδne (IsDiscreteValuationRing.addVal_eq_top_iff.mp htop)
  have hord : (localDifferentOrder (p := p) (L := L) : ℕ∞) =
      IsDiscreteValuationRing.addVal (Integers L)
        (localDifferentGenerator (p := p) (L := L)) := by
    unfold localDifferentOrder
    exact ENat.coe_toNat hfin
  rw [Ideal.mem_span_singleton, ← IsDiscreteValuationRing.addVal_le_iff_dvd, ← hord]
  have hpval : IsDiscreteValuationRing.addVal (Integers L) (p : Integers L) =
      (logShellRamificationExponent (K := L) (p := p) : ℕ∞) := by
    simpa [ramifiedPrimeAddVal] using
      addVal_prime_eq_ramificationExponent (K := L) (p := p)
  have hpm : IsDiscreteValuationRing.addVal (Integers L) ((p : Integers L) ^ m) =
      ((m * logShellRamificationExponent (K := L) (p := p) : ℕ) : ℕ∞) := by
    rw [IsDiscreteValuationRing.addVal_pow, hpval]
    simp [nsmul_eq_mul, Nat.cast_mul]
  rw [hpm]
  have hepos : 0 < logShellRamificationExponent (K := L) (p := p) :=
    logShellRamificationExponent_pos (K := L) (p := p)
  have hleReal : (localDifferentOrder (p := p) (L := L) : ℝ) ≤
      (m * logShellRamificationExponent (K := L) (p := p) : ℕ) := by
    have hepos' : (0 : ℝ) < (logShellRamificationExponent (K := L) (p := p) : ℝ) := by
      exact_mod_cast hepos
    have hdiv : (localDifferentOrder (p := p) (L := L) : ℝ) /
        (logShellRamificationExponent (K := L) (p := p) : ℝ) ≤ (m : ℝ) := hm
    have hmul := (div_le_iff₀ hepos').mp hdiv
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hnat : localDifferentOrder (p := p) (L := L) ≤
      m * logShellRamificationExponent (K := L) (p := p) := by
    exact_mod_cast hleReal
  exact_mod_cast hnat

/-- The unit ideal of `Integers L` agrees with the actual valuation integer lattice. -/
theorem restrictScalars_one_eq_valuationIntegerLattice :
    (1 : Submodule (Integers L) L).restrictScalars ℤ_[p] =
      valuationIntegerLattice (K := L) (p := p) := by
  ext x
  constructor
  · intro hx
    change x ∈ (1 : Submodule (Integers L) L) at hx
    rw [Submodule.mem_one] at hx
    obtain ⟨y, rfl⟩ := hx
    exact y.property
  · intro hx
    change x ∈ (1 : Submodule (Integers L) L)
    rw [Submodule.mem_one]
    exact ⟨⟨x, hx⟩, rfl⟩

/-- A generator of the local different satisfies `delta * O^*` inside `O` for the
local integral trace dual `O^*`.  This is the element form of `D_L * O^* = O`. -/
theorem localDifferentGenerator_mul_mem_integralTraceDual
    {x : L}
    (hx : x ∈ padicIntegralTraceDualLattice (Algebra.traceForm ℚ_[p] L)
      (valuationIntegerLattice (K := L) (p := p))) :
    (localDifferentGenerator (p := p) (L := L) : L) * x ∈
      valuationIntegerLattice (K := L) (p := p) := by
  haveI : IsIntegrallyClosed ℤ_[p] := padicInt_isIntegrallyClosed (p := p)
  haveI : IsDedekindDomain (Integers L) := integersIsDedekindDomain (p := p) (L := L)
  haveI : Module.IsTorsionFree ℤ_[p] (Integers L) := integersIsTorsionFree (p := p) (L := L)
  haveI : IsIntegralClosure (Integers L) ℤ_[p] L :=
    integersIsIntegralClosure (p := p) (L := L)
  have hD := coeSubmodule_differentIdeal_eq_inv_traceDual
    (A := ℤ_[p]) (K := ℚ_[p]) (B := Integers L) (L := L)
  have hδ : (localDifferentGenerator (p := p) (L := L) : L) ∈
      (1 / Submodule.traceDual ℤ_[p] ℚ_[p] (1 : Submodule (Integers L) L) :
        Submodule (Integers L) L) := by
    rw [← hD]
    exact ⟨_, localDifferentGenerator_mem (p := p) (L := L), rfl⟩
  have hx' : x ∈ Submodule.traceDual ℤ_[p] ℚ_[p] (1 : Submodule (Integers L) L) := by
    have hx'' : x ∈ integralTraceDualLattice (R := ℤ_[p]) (S := ℚ_[p])
        (Algebra.traceForm ℚ_[p] L) (valuationIntegerLattice (K := L) (p := p)) := hx
    rw [← restrictScalars_one_eq_valuationIntegerLattice] at hx''
    rw [integralTraceDualLattice_traceForm_eq_traceDual] at hx''
    exact hx''
  have hmul : (localDifferentGenerator (p := p) (L := L) : L) * x ∈
      (1 : Submodule (Integers L) L) := by
    have h := (Submodule.mem_div_iff_forall_mul_mem.mp hδ) x hx'
    exact h
  rw [← restrictScalars_one_eq_valuationIntegerLattice]
  exact hmul

end LocalDifferent

/-! ## The tensor different generator and the element inclusion -/

/-- The actual tensor different generator `δ = ⊗_i δ_i`, where `δ_i` is the
chosen generator of the local different ideal.  Its valuation is the full
`d_I = ∑_i d_i`; the fixed-star `d_{I*}` version would require an extra
`p^{d_*}` factor and is not asserted here. -/
noncomputable def arithmeticTensorDifferentGenerator :
    ArithmeticTensorTupleBlock places tuple :=
  PiTensorProduct.tprod ℚ_[p]
    (fun i => (localDifferentGenerator (p := p)
      (L := arithmeticTupleLocalField places tuple i) :
        arithmeticTupleLocalField places tuple i))

theorem arithmeticTupleValuationIntegerQpBasis_apply
    (j : (i : ι) → arithmeticTupleLocalBasisIndex places tuple i) :
    arithmeticTupleValuationIntegerQpBasis places tuple j =
      PiTensorProduct.tprod ℚ_[p]
        (fun i => arithmeticTupleLocalQpBasis places tuple i (j i)) := by
  rw [arithmeticTupleValuationIntegerQpBasis_eq_piTensorProduct]
  exact Basis.piTensorProduct_apply _ j

theorem arithmeticTupleValuationIntegerDualQpBasis_apply
    (k : (i : ι) → arithmeticTupleLocalBasisIndex places tuple i) :
    arithmeticTupleValuationIntegerDualQpBasis places tuple k =
      PiTensorProduct.tprod ℚ_[p]
        (fun i => arithmeticTupleLocalDualQpBasis places tuple i (k i)) := by
  rw [arithmeticTupleValuationIntegerDualQpBasis]
  exact Basis.piTensorProduct_apply _ k

theorem arithmeticTupleTraceForm_dualBasis_apply
    (j k : (i : ι) → arithmeticTupleLocalBasisIndex places tuple i) :
    Algebra.traceForm ℚ_[p] (ArithmeticTensorTupleBlock places tuple)
        (arithmeticTupleValuationIntegerDualQpBasis places tuple k)
        (arithmeticTupleValuationIntegerQpBasis places tuple j) =
      if k = j then (1 : ℚ_[p]) else 0 := by
  rw [Algebra.traceForm_apply,
    arithmeticTupleValuationIntegerDualQpBasis_apply,
    arithmeticTupleValuationIntegerQpBasis_apply]
  change Algebra.trace ℚ_[p] (⨂[ℚ_[p]] i, arithmeticTupleLocalField places tuple i)
      ((PiTensorProduct.tprod ℚ_[p]
          (fun i => arithmeticTupleLocalDualQpBasis places tuple i (k i))) *
        (PiTensorProduct.tprod ℚ_[p]
          (fun i => arithmeticTupleLocalQpBasis places tuple i (j i)))) =
    if k = j then (1 : ℚ_[p]) else 0
  rw [PiTensorProduct.tprod_mul_tprod, piTensorProduct_trace_tprod]
  have hfac : ∀ i, Algebra.trace ℚ_[p] (arithmeticTupleLocalField places tuple i)
      (arithmeticTupleLocalDualQpBasis places tuple i (k i) *
        arithmeticTupleLocalQpBasis places tuple i (j i)) =
      if k i = j i then (1 : ℚ_[p]) else 0 := by
    intro i
    rw [← Algebra.traceForm_apply]
    unfold arithmeticTupleLocalDualQpBasis
    rw [LinearMap.BilinForm.apply_dualBasis_left]
    by_cases h : j i = k i
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  simp only [Pi.mul_apply]
  rw [show (∏ i, Algebra.trace ℚ_[p] (arithmeticTupleLocalField places tuple i)
        (arithmeticTupleLocalDualQpBasis places tuple i (k i) *
          arithmeticTupleLocalQpBasis places tuple i (j i))) =
      ∏ i, (if k i = j i then (1 : ℚ_[p]) else 0) from
    Finset.prod_congr rfl fun i _ => hfac i]
  rw [Finset.prod_boole]
  simp [funext_iff]

/-- The tensor trace dual of `R_I` is exactly the lattice spanned by the tensor
dual basis. -/
theorem arithmeticTupleValuationIntegerTraceDual_eq_basisIntegralLattice :
    padicIntegralTraceDualLattice
        (Algebra.traceForm ℚ_[p] (ArithmeticTensorTupleBlock places tuple))
        (arithmeticTupleValuationIntegerLattice places tuple) =
      basisIntegralLattice (arithmeticTupleValuationIntegerDualQpBasis places tuple) := by
  classical
  rw [arithmeticTupleValuationIntegerLattice_eq_basisIntegralLattice]
  exact padicIntegralTraceDualLattice_basisIntegralLattice_eq_basisIntegralLattice
    (B := Algebra.traceForm ℚ_[p] (ArithmeticTensorTupleBlock places tuple))
    (arithmeticTupleValuationIntegerQpBasis places tuple)
    (arithmeticTupleValuationIntegerDualQpBasis places tuple)
    (fun j k => arithmeticTupleTraceForm_dualBasis_apply places tuple j k)

/-- The local integral lattice is spanned by the local rational basis. -/
theorem arithmeticTupleLocalIntegerLattice_eq_basisIntegralLattice (i : ι) :
    arithmeticTupleLocalIntegerLattice places tuple i =
      basisIntegralLattice (arithmeticTupleLocalQpBasis places tuple i) :=
  (basisIntegralLattice_padicBasisOfIntegralBasis
    (arithmeticTupleLocalIntegerLattice places tuple i)
    (Module.Free.chooseBasis ℤ_[p] (arithmeticTupleLocalIntegerLattice places tuple i))
    (span_padic_valuationIntegerLattice_eq_top
      (K := arithmeticTupleLocalField places tuple i) (p := p))).symm

/-- The local trace dual is spanned by the local dual basis. -/
theorem arithmeticTupleLocalTraceDual_eq_basisIntegralLattice (i : ι) :
    padicIntegralTraceDualLattice
        (Algebra.traceForm ℚ_[p] (arithmeticTupleLocalField places tuple i))
        (arithmeticTupleLocalIntegerLattice places tuple i) =
      basisIntegralLattice (arithmeticTupleLocalDualQpBasis places tuple i) := by
  classical
  rw [arithmeticTupleLocalIntegerLattice_eq_basisIntegralLattice]
  exact padicIntegralTraceDualLattice_basisIntegralLattice_eq_basisIntegralLattice
    (B := Algebra.traceForm ℚ_[p] (arithmeticTupleLocalField places tuple i))
    (arithmeticTupleLocalQpBasis places tuple i)
    (arithmeticTupleLocalDualQpBasis places tuple i)
    (fun j k => by
      unfold arithmeticTupleLocalDualQpBasis
      rw [LinearMap.BilinForm.apply_dualBasis_left]
      by_cases h : j = k
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (Ne.symm h)])

/-- Each local dual basis vector lies in the local integral trace dual. -/
theorem arithmeticTupleLocalDualQpBasis_mem_traceDual (i : ι)
    (ki : arithmeticTupleLocalBasisIndex places tuple i) :
    arithmeticTupleLocalDualQpBasis places tuple i ki ∈
      padicIntegralTraceDualLattice
        (Algebra.traceForm ℚ_[p] (arithmeticTupleLocalField places tuple i))
        (arithmeticTupleLocalIntegerLattice places tuple i) := by
  rw [arithmeticTupleLocalTraceDual_eq_basisIntegralLattice]
  exact Submodule.subset_span ⟨ki, rfl⟩

/-- The local different generator times a local dual basis vector is integral. -/
theorem arithmeticTupleLocalDifferent_mul_dualQpBasis_mem_lattice (i : ι)
    (ki : arithmeticTupleLocalBasisIndex places tuple i) :
    (localDifferentGenerator (p := p) (L := arithmeticTupleLocalField places tuple i) :
        arithmeticTupleLocalField places tuple i) *
      arithmeticTupleLocalDualQpBasis places tuple i ki ∈
        arithmeticTupleLocalIntegerLattice places tuple i :=
  localDifferentGenerator_mul_mem_integralTraceDual
    (p := p) (L := arithmeticTupleLocalField places tuple i)
    (arithmeticTupleLocalDualQpBasis_mem_traceDual places tuple i ki)

/-- The tensor different generator times a tensor dual basis vector is integral. -/
theorem arithmeticTensorDifferentGenerator_mul_dualQpBasis_mem_lattice
    (k : (i : ι) → arithmeticTupleLocalBasisIndex places tuple i) :
    arithmeticTensorDifferentGenerator places tuple *
      arithmeticTupleValuationIntegerDualQpBasis places tuple k ∈
        arithmeticTupleValuationIntegerLattice places tuple := by
  have hmul : arithmeticTensorDifferentGenerator places tuple *
      arithmeticTupleValuationIntegerDualQpBasis places tuple k =
      PiTensorProduct.tprod ℚ_[p]
        (fun i => (localDifferentGenerator (p := p)
          (L := arithmeticTupleLocalField places tuple i) :
            arithmeticTupleLocalField places tuple i) *
          arithmeticTupleLocalDualQpBasis places tuple i (k i)) := by
    rw [arithmeticTensorDifferentGenerator,
      arithmeticTupleValuationIntegerDualQpBasis_apply]
    change (PiTensorProduct.tprod ℚ_[p]
        (fun i => (localDifferentGenerator (p := p)
          (L := arithmeticTupleLocalField places tuple i) :
            arithmeticTupleLocalField places tuple i))) *
        (PiTensorProduct.tprod ℚ_[p]
          (fun i => arithmeticTupleLocalDualQpBasis places tuple i (k i))) = _
    exact PiTensorProduct.tprod_mul_tprod _ _
  rw [hmul, arithmeticTupleValuationIntegerLattice_eq_span]
  refine Submodule.subset_span ⟨
    fun i => (localDifferentGenerator (p := p)
      (L := arithmeticTupleLocalField places tuple i) :
        arithmeticTupleLocalField places tuple i) *
      arithmeticTupleLocalDualQpBasis places tuple i (k i), ?_, ?_⟩
  · intro i _
    exact arithmeticTupleLocalDifferent_mul_dualQpBasis_mem_lattice places tuple i (k i)
  · rfl

/-- The tensor different generator multiplies the full integral trace dual into `R_I`. -/
theorem arithmeticTensorDifferentGenerator_mul_mem_traceDual
    {x : ArithmeticTensorTupleBlock places tuple}
    (hx : x ∈ padicIntegralTraceDualLattice
      (Algebra.traceForm ℚ_[p] (ArithmeticTensorTupleBlock places tuple))
      (arithmeticTupleValuationIntegerLattice places tuple)) :
    arithmeticTensorDifferentGenerator places tuple * x ∈
      arithmeticTupleValuationIntegerLattice places tuple := by
  classical
  have hx' : x ∈
      basisIntegralLattice (arithmeticTupleValuationIntegerDualQpBasis places tuple) := by
    rwa [← arithmeticTupleValuationIntegerTraceDual_eq_basisIntegralLattice]
  rw [basisIntegralLattice] at hx'
  refine Submodule.span_induction
    (p := fun x _ => arithmeticTensorDifferentGenerator places tuple * x ∈
      arithmeticTupleValuationIntegerLattice places tuple) ?_ ?_ ?_ ?_ hx'
  · intro y hy
    rcases hy with ⟨k, rfl⟩
    exact arithmeticTensorDifferentGenerator_mul_dualQpBasis_mem_lattice places tuple k
  · rw [mul_zero]
    exact (arithmeticTupleValuationIntegerLattice places tuple).zero_mem
  · intro y z hy hz hy' hz'
    rw [mul_add]
    exact (arithmeticTupleValuationIntegerLattice places tuple).add_mem hy' hz'
  · intro a y hy hy'
    rw [Algebra.mul_smul_comm]
    exact (arithmeticTupleValuationIntegerLattice places tuple).smul_mem a hy'

/-- The element-form inclusion `δ • (R_I)~ ⊆ R_I` for the actual tensor
different generator.  This is the full-product `d_I = ∑_i d_i` form. -/
theorem arithmeticTensorDifferentGenerator_mul_mem_arithmeticTupleValuationIntegerLattice
    {x : ArithmeticTensorTupleBlock places tuple}
    (hx : x ∈ arithmeticTupleValuationIntegerNormalization places tuple) :
    arithmeticTensorDifferentGenerator places tuple * x ∈
      arithmeticTupleValuationIntegerLattice places tuple :=
  arithmeticTensorDifferentGenerator_mul_mem_traceDual places tuple
    (arithmeticTupleValuationIntegerNormalization_le_traceDual places tuple hx)

/-- The same inclusion with the canonical holomorphic unit reference `O_hol`. -/
theorem arithmeticTensorDifferentGenerator_mul_mem_of_mem_arithmeticTupleCanonicalUnitReference
    {x : ArithmeticTensorTupleBlock places tuple}
    (hx : x ∈ arithmeticTupleCanonicalUnitReference places tuple) :
    arithmeticTensorDifferentGenerator places tuple * x ∈
      arithmeticTupleValuationIntegerLattice places tuple := by
  rw [arithmeticTupleCanonicalUnitReference_eq_integralClosure] at hx
  exact arithmeticTensorDifferentGenerator_mul_mem_arithmeticTupleValuationIntegerLattice
    places tuple hx

/-- Multiplication of a `Zp`-submodule of the tensor by the actual tensor
different generator.  This is the elementwise `δ • N` used in the paper form. -/
noncomputable def arithmeticTensorDifferentGeneratorMulSubmodule
    (N : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
    Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple) :=
  N.map ((LinearMap.mulLeft ℚ_[p]
    (arithmeticTensorDifferentGenerator places tuple)).restrictScalars ℤ_[p])

/-- The carrier of the normalization submodule is exactly the canonical
holomorphic unit reference `O_hol`. -/
theorem arithmeticTupleValuationIntegerNormalization_toSubmodule_eq_canonicalUnitReference :
    ((arithmeticTupleValuationIntegerNormalization places tuple).toSubmodule :
        Set (ArithmeticTensorTupleBlock places tuple)) =
      arithmeticTupleCanonicalUnitReference places tuple := by
  rw [arithmeticTupleCanonicalUnitReference_eq_integralClosure]
  rfl

/-- Paper-form integer scalar consequence of the different inclusion.

The hypothesis `hdiff` is the explicit order-to-scalar bridge
`p^{⌈∑ d_i⌉} • O_hol ≤ δ • O_hol`.  It is not proved here: the present file
constructs the actual generator `δ = ⊗ δ_i`, but does not identify the
tensor prime-power scalar with the tensor of the local divisibility relations.
Given that bridge, the already-proved element inclusion `δ • O_hol ⊆ R_I`
immediately yields the IUT IV Prop. 1.1 integer-scalar form. -/
theorem arithmeticTensorPaperDifferentScale
    (d : ι → ℝ)
    (hdiff : arithmeticTensorPrimePowerScale places tuple ⌈∑ i, d i⌉
        (arithmeticTupleValuationIntegerNormalization places tuple).toSubmodule ≤
      arithmeticTensorDifferentGeneratorMulSubmodule places tuple
        (arithmeticTupleValuationIntegerNormalization places tuple).toSubmodule) :
    arithmeticTensorPrimePowerScale places tuple ⌈∑ i, d i⌉
        (arithmeticTupleValuationIntegerNormalization places tuple).toSubmodule ≤
      arithmeticTupleValuationIntegerLattice places tuple := by
  refine hdiff.trans ?_
  rintro y ⟨x, hx, rfl⟩
  have hxO : x ∈ arithmeticTupleCanonicalUnitReference places tuple := by
    rw [← arithmeticTupleValuationIntegerNormalization_toSubmodule_eq_canonicalUnitReference]
    exact hx
  exact arithmeticTensorDifferentGenerator_mul_mem_of_mem_arithmeticTupleCanonicalUnitReference
    places tuple hxO

end

end LeanFormal.IUT.IntegralTraceDualTensorInclusion


