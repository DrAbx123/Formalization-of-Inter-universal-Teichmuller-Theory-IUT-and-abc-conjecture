import Mathlib.RingTheory.Etale.Field
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.LinearAlgebra.PiTensorProduct.Finite

/-!
# Field-product decomposition at a finite tensor-packet level

The finite-factor algebraic step in IUT III Proposition 3.1(i), used before
applying the coordinatewise hull construction in `LocalFieldProductHull`.
For finite extensions of a characteristic-zero field the actual tensor
algebra is a finite product of finite separable field extensions. This uses
Mathlib's finite etale classification, not a multiplication-image model.

Only the algebraic statement is asserted here. Transport of local-field norms,
the topology, integral structures and the source ind-system is separate.
-/

open scoped TensorProduct

namespace LeanFormal.IUT.LocalFieldTensorDecomposition

universe u

section FiniteTensor

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]

/-- The product of a family of algebra maps induces an algebra map from
the actual tensor algebra to a commutative algebra. -/
noncomputable def liftFactorAlgHoms {B : Type u} [CommRing B] [Algebra R B]
    (f : (i : ι) → A i →ₐ[R] B) : (⨂[R] i, A i) →ₐ[R] B :=
  PiTensorProduct.liftAlgHom
    ((MultilinearMap.mkPiAlgebra R ι B).compLinearMap (fun i => (f i).toLinearMap))
    (by simp)
    (by intro x y; simp [Finset.prod_mul_distrib])

theorem liftFactorAlgHoms_comp_single [DecidableEq ι]
    {B : Type u} [CommRing B] [Algebra R B] (f : (i : ι) → A i →ₐ[R] B) (i : ι) :
    (liftFactorAlgHoms f).comp (PiTensorProduct.singleAlgHom i) = f i := by
  ext x
  suffices hprod : (∏ j, f j (Function.update (1 : (j : ι) → A j) i x j)) = f i x by
    simpa [liftFactorAlgHoms, PiTensorProduct.singleAlgHom, Pi.mulSingle] using hprod
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

omit [Fintype ι] in
/-- Formal etaleness of a finite tensor algebra is proved by constructing
the unique lift one factor at a time through a square-zero quotient. -/
theorem finiteTensor_formallyEtale [Finite ι] [∀ i, Algebra.FormallyEtale R (A i)] :
    Algebra.FormallyEtale R (⨂[R] i, A i) := by
  classical
  letI := Fintype.ofFinite ι
  apply Algebra.FormallyEtale.iff_comp_bijective.mpr
  intro B _ _ I hI
  constructor
  · intro f g hfg
    apply PiTensorProduct.algHom_ext
    intro i
    apply (Algebra.FormallyEtale.comp_bijective R (A i) I hI).injective
    simpa only [AlgHom.comp_assoc] using
      congrArg (fun h => h.comp (PiTensorProduct.singleAlgHom i)) hfg
  · intro f
    have hfactor : ∀ i, ∃ g : A i →ₐ[R] B,
        (Ideal.Quotient.mkₐ R I).comp g = f.comp (PiTensorProduct.singleAlgHom i) :=
      fun i => (Algebra.FormallyEtale.comp_bijective R (A i) I hI).surjective _
    choose g hg using hfactor
    refine ⟨liftFactorAlgHoms g, ?_⟩
    apply PiTensorProduct.algHom_ext
    intro i
    rw [AlgHom.comp_assoc, liftFactorAlgHoms_comp_single]
    exact hg i

end FiniteTensor

/-- Finite characteristic-zero field extensions are etale, with the
separability and finite-presentation prerequisites supplied by Mathlib. -/
theorem finiteExtension_etale (k K : Type u) [Field k] [Field K] [CharZero k]
    [Algebra k K] [FiniteDimensional k K] : Algebra.Etale k K := by
  letI : Algebra.FormallyEtale k K := Algebra.FormallyEtale.of_isSeparable k K
  exact ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

/-- Actual two-factor tensor algebra decomposition. Every output factor is
a finite separable extension of the same base field. -/
theorem exists_finiteFieldProduct_tensor (k K L : Type u)
    [Field k] [Field K] [Field L] [CharZero k]
    [Algebra k K] [Algebra k L] [FiniteDimensional k K] [FiniteDimensional k L] :
    ∃ (J : Type u) (_ : Finite J) (E : J → Type u) (_ : ∀ j, Field (E j))
      (_ : ∀ j, Algebra k (E j)) (_ : (K ⊗[k] L) ≃ₐ[k] ((j : J) → E j)),
      ∀ j, Module.Finite k (E j) ∧ Algebra.IsSeparable k (E j) := by
  letI : Algebra.Etale k K := finiteExtension_etale k K
  letI : Algebra.Etale k L := finiteExtension_etale k L
  letI : Algebra.Etale k (K ⊗[k] L) := Algebra.Etale.comp k K (K ⊗[k] L)
  exact (Algebra.Etale.iff_exists_algEquiv_prod k (K ⊗[k] L)).mp inferInstance

/-- The finite-level algebraic field decomposition for an arbitrary finite
tensor packet. Neither the tensor factors nor the resulting fields are
collapsed into a single common field. Topological compatibility remains separate. -/
theorem exists_finiteFieldProduct_piTensor (k : Type u) [Field k] [CharZero k]
    {ι : Type u} [Finite ι] (K : ι → Type u) [∀ i, Field (K i)]
    [∀ i, Algebra k (K i)] [∀ i, FiniteDimensional k (K i)] :
    ∃ (J : Type u) (_ : Finite J) (E : J → Type u) (_ : ∀ j, Field (E j))
      (_ : ∀ j, Algebra k (E j)) (_ : (⨂[k] i, K i) ≃ₐ[k] ((j : J) → E j)),
      ∀ j, Module.Finite k (E j) ∧ Algebra.IsSeparable k (E j) := by
  letI := Fintype.ofFinite ι
  letI : ∀ i, Algebra.FormallyEtale k (K i) :=
    fun i => Algebra.FormallyEtale.of_isSeparable k (K i)
  letI : Algebra.FormallyEtale k (⨂[k] i, K i) := finiteTensor_formallyEtale
  letI : Algebra.Etale k (⨂[k] i, K i) :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  exact (Algebra.Etale.iff_exists_algEquiv_prod k (⨂[k] i, K i)).mp inferInstance

end LeanFormal.IUT.LocalFieldTensorDecomposition
