import tmp.sheaf.xif.paper.S1849RPrimeReflectCompleteActual
import Mathlib.RingTheory.Trace.Quotient
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Etale.Field
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
open scoped Matrix
open LinearMap

namespace LeanFormal.IUT.XiFPaper.S1853FieldCaseActual

lemma trace_pi_apply {k : Type*} [Field k] {ι : Type*} [Fintype ι] (x : ι → k) :
    Algebra.trace k (ι → k) x = ∑ i, x i := by
  classical
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun k ι)]
  have hdiag : Algebra.leftMulMatrix (Pi.basisFun k ι) x = Matrix.diagonal x := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, Pi.basisFun_repr]
    by_cases h : i = j
    · subst h
      simp [Pi.mul_apply, Pi.basisFun_apply]
    · simp [Pi.mul_apply, Pi.basisFun_apply, h]
  rw [hdiag]
  simp [Matrix.trace]

lemma traceForm_pi_apply {k : Type*} [Field k] {ι : Type*} [Fintype ι] (x y : ι → k) :
    Algebra.traceForm k (ι → k) x y = ∑ i, x i * y i := by
  rw [Algebra.traceForm_apply, trace_pi_apply]
  simp [Pi.mul_apply]

lemma sum_mul_single_eq {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → k) (i : ι) :
    (∑ j, x j * (Pi.single i 1 : ι → k) j) = x i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · intro hi
    simp at hi

lemma traceForm_pi_nondegenerate {k : Type*} [Field k] {ι : Type*} [Fintype ι] :
    (Algebra.traceForm k (ι → k)).Nondegenerate := by
  classical
  constructor
  · intro x hx
    by_contra hx0
    have hex : ∃ i, x i ≠ 0 := by
      by_contra h
      apply hx0
      funext i
      by_contra hi
      exact h ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    have h := hx (Pi.single i 1)
    rw [traceForm_pi_apply, sum_mul_single_eq] at h
    exact hi h
  · intro y hy
    by_contra hy0
    have hex : ∃ i, y i ≠ 0 := by
      by_contra h
      apply hy0
      funext i
      by_contra hi
      exact h ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    have h := hy (Pi.single i 1)
    rw [traceForm_pi_apply] at h
    have hsum : (∑ j, (Pi.single i 1 : ι → k) j * y j) = y i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Pi.single_eq_of_ne hji]
      · intro hi'
        simp at hi'
    rw [hsum] at h
    exact hi h

lemma traceForm_baseChange
    (k Ω A : Type*) [Field k] [CommRing Ω] [Algebra k Ω] [CommRing A] [Algebra k A]
    [Module.Finite k A] :
    (Algebra.traceForm k A).baseChange Ω = Algebra.traceForm Ω (Ω ⊗[k] A) := by
  apply BilinForm.ext
  intro x y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x z hx hz =>
    simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul a x =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz =>
      simp only [map_add, hy, hz]
    | tmul b y =>
      rw [BilinForm.baseChange_tmul]
      change Algebra.trace k A (x * y) • (a * b) =
        Algebra.trace Ω (Ω ⊗[k] A) ((a ⊗ₜ[k] x) * (b ⊗ₜ[k] y))
      rw [show (a ⊗ₜ[k] x) * (b ⊗ₜ[k] y) = (a * b) ⊗ₜ[k] (x * y) by
        rw [Algebra.TensorProduct.tmul_mul_tmul]]
      rw [show (a * b) ⊗ₜ[k] (x * y) = (a * b) • ((1 : Ω) ⊗ₜ[k] (x * y)) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
      rw [map_smul, smul_eq_mul]
      conv_lhs => rw [Algebra.trace_apply]
      conv_rhs => rw [Algebra.trace_apply]
      have h := LinearMap.trace_baseChange (R := k) (M := A)
        (f := Algebra.lmul k A (x * y)) Ω
      rw [Algebra.baseChange_lmul] at h
      rw [h]
      simp [Algebra.smul_def, mul_comm, mul_assoc]

lemma nondegenerate_of_baseChange
    (k Ω A : Type*) [Field k] [Field Ω] [Algebra k Ω] [CommRing A] [Algebra k A]
    (h : ((Algebra.traceForm k A).baseChange Ω).Nondegenerate) :
    (Algebra.traceForm k A).Nondegenerate := by
  haveI : Module.FaithfullyFlat k Ω := inferInstance
  constructor
  · intro x hx
    have h0 : (1 : Ω) ⊗ₜ[k] x = 0 := by
      apply h.1 ((1 : Ω) ⊗ₜ[k] x)
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp [hz, hw]
      | tmul c y =>
        rw [BilinForm.baseChange_tmul]
        simp [hx y]
    exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := k) (B := Ω) (M := A)
      (by simpa using h0)
  · intro y hy
    have h0 : (1 : Ω) ⊗ₜ[k] y = 0 := by
      apply h.2 ((1 : Ω) ⊗ₜ[k] y)
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp [hz, hw]
      | tmul c x =>
        rw [BilinForm.baseChange_tmul]
        simp [hy x]
    exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := k) (B := Ω) (M := A)
      (by simpa using h0)

/-- Trace form perfectness for finite etale algebras over a field. -/
theorem traceForm_nondegenerate_of_field
    {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    [Algebra.Etale k A] :
    (Algebra.traceForm k A).Nondegenerate := by
  classical
  haveI : Module.Finite k A := Algebra.FormallyUnramified.finite_of_free k A
  let Ω := AlgebraicClosure k
  let AΩ := Ω ⊗[k] A
  haveI : Algebra.Etale Ω AΩ := Algebra.Etale.baseChange k A Ω
  haveI : Module.Finite Ω AΩ := inferInstance
  haveI : Algebra.EssFiniteType Ω AΩ := inferInstance
  haveI : IsSepClosed Ω := IsSepClosed.of_isAlgClosed Ω
  haveI : IsArtinianRing AΩ := IsArtinianRing.of_finite Ω AΩ
  haveI : Fintype (PrimeSpectrum AΩ) := Fintype.ofFinite _
  let e : AΩ ≃ₐ[Ω] (PrimeSpectrum AΩ → Ω) :=
    Algebra.FormallyEtale.equivPiOfIsSepClosed Ω AΩ
  have hpi : (Algebra.traceForm Ω (PrimeSpectrum AΩ → Ω)).Nondegenerate :=
    traceForm_pi_nondegenerate
  have hcongr : Algebra.traceForm Ω (PrimeSpectrum AΩ → Ω) =
      BilinForm.congr e.toLinearEquiv (Algebra.traceForm Ω AΩ) := by
    apply BilinForm.ext
    intro x y
    rw [BilinForm.congr_apply]
    rw [Algebra.traceForm_apply, Algebra.traceForm_apply]
    have hxy : e (e.symm x * e.symm y) = x * y := by simp
    calc Algebra.trace Ω (PrimeSpectrum AΩ → Ω) (x * y)
        = Algebra.trace Ω (PrimeSpectrum AΩ → Ω) (e (e.symm x * e.symm y)) := by rw [hxy]
      _ = Algebra.trace Ω AΩ (e.symm x * e.symm y) := Algebra.trace_eq_of_algEquiv e _
  have hAΩ : (Algebra.traceForm Ω AΩ).Nondegenerate := by
    rw [← (BilinForm.nondegenerate_congr_iff e.toLinearEquiv)]
    rw [← hcongr]
    exact hpi
  rw [← traceForm_baseChange k Ω A] at hAΩ
  exact nondegenerate_of_baseChange k Ω A hAΩ

end LeanFormal.IUT.XiFPaper.S1853FieldCaseActual
