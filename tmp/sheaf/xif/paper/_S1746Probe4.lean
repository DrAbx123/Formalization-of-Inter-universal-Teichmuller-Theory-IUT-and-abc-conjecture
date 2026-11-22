import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Etale.Descent
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.Etale.Finite

noncomputable section

open scoped TensorProduct

namespace S1746Probe

universe u v w

theorem finiteSplit_of_injective_pi {K : Type u} [Field K] {R : Type v} [CommRing R] [Algebra K R]
    {ι : Type w} [Finite ι] (f : R →ₐ[K] (ι → K)) (hf : Function.Injective f) :
    Algebra.IsFiniteSplit K R := by
  classical
  by_cases hR : Subsingleton R
  · exact Algebra.IsFiniteSplit.of_subsingleton_top
  haveI : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
  have hι : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    haveI : IsEmpty ι := h
    exact hR (hf.subsingleton)
  let p (i : ι) : R →ₐ[K] K := (Pi.evalAlgHom K (fun _ : ι => K) i).comp f
  have hp_surj (i : ι) : Function.Surjective (p i) := by
    intro x
    refine ⟨algebraMap K R x, ?_⟩
    simp [p]
  have hp_max (i : ι) : (RingHom.ker (p i)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective (p i) (hp_surj i)
  let σ : Type v := ↥(Set.range fun i : ι => RingHom.ker (p i))
  haveI : Fintype σ := Fintype.ofFinite σ
  let rep (I : σ) : ι := Classical.choose I.property
  have rep_spec (I : σ) : RingHom.ker (p (rep I)) = (I : Ideal R) :=
    Classical.choose_spec I.property
  have hmax (I : σ) : (I : Ideal R).IsMaximal := by
    rw [← rep_spec I]
    exact hp_max (rep I)
  have hcoprime : Pairwise (Function.onFun IsCoprime (fun I : σ => (I : Ideal R))) := by
    intro I J hIJ
    haveI := hmax I
    haveI := hmax J
    exact Ideal.isCoprime_of_isMaximal (by intro h; exact hIJ (Subtype.ext h))
  have hinf : (⨅ I : σ, (I : Ideal R)) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Submodule.mem_bot]
    apply hf
    ext i
    have hx' : x ∈ (⨅ I : σ, (I : Ideal R)) := hx
    have hxker : x ∈ RingHom.ker (p i) :=
      (Submodule.mem_iInf _).mp hx' ⟨RingHom.ker (p i), ⟨i, rfl⟩⟩
    simpa [p] using hxker
  let fI : σ → Ideal R := fun I => (I : Ideal R)
  let Iinf : Ideal R := ⨅ I : σ, fI I
  let e_crt_ring : R ⧸ Iinf ≃+* ((I : σ) → R ⧸ fI I) :=
    Ideal.quotientInfRingEquivPiQuotient fI hcoprime
  let e_crt := AlgEquiv.ofRingEquiv (R := K) (f := e_crt_ring) (by
    intro x
    ext I
    trans Ideal.Quotient.mk (fI I) (algebraMap K R x)
    · rw [← Ideal.Quotient.mk_algebraMap]
      exact congrFun (Ideal.quotientInfToPiQuotient_mk fI (algebraMap K R x)) I
    · rfl)
  let qe (I : σ) := (Ideal.quotientEquivAlgOfEq K (rep_spec I).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := p (rep I)) (hp_surj (rep I)))
  let e3 := AlgEquiv.piCongrRight (fun I : σ => qe I)
  let e1 := (AlgEquiv.quotientBot K R).symm.trans (Ideal.quotientEquivAlgOfEq K hinf).symm
  let e := e1.trans (e_crt.trans e3)
  exact ⟨Fintype.card σ, ⟨e.trans (AlgEquiv.piCongrLeft' K (fun _ : σ => K) (Fintype.equivFin σ))⟩⟩

theorem etale_subalgebra {K : Type u} [Field K] {A : Type v} [CommRing A] [Algebra K A]
    [Module.Finite K A] [Algebra.Etale K A] (B : Subalgebra K A) :
    Algebra.Etale K B := by
  classical
  let Kbar := AlgebraicClosure K
  haveI : IsSepClosed Kbar := inferInstance
  haveI : Module.FaithfullyFlat K Kbar := inferInstance
  let i : Kbar ⊗[K] B →ₐ[Kbar] Kbar ⊗[K] A := Algebra.TensorProduct.lTensor Kbar B.val
  have hi : Function.Injective i := by
    intro x y h
    have hlin : Function.Injective (LinearMap.lTensor Kbar B.val.toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := Kbar) B.val.toLinearMap Subtype.val_injective
    exact hlin h
  haveI : Algebra.IsFiniteSplit Kbar (Kbar ⊗[K] A) := inferInstance
  obtain ⟨n, ⟨eA⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun Kbar (Kbar ⊗[K] A)
  let f : Kbar ⊗[K] B →ₐ[Kbar] (Fin n → Kbar) := eA.toAlgHom.comp i
  have hf : Function.Injective f := eA.injective.comp hi
  haveI : Algebra.IsFiniteSplit Kbar (Kbar ⊗[K] B) :=
    finiteSplit_of_injective_pi (K := Kbar) (R := Kbar ⊗[K] B) (ι := Fin n) f hf
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat (R := K) (S := B) Kbar

variable {K : Type u} [Field K]
def fixedSubalgebra {G : Type u} [Group G] {X : CommAlgCat.FiniteEtale.{0} K}
    (φ : G → (X →ₐ[K] X)) : Subalgebra K X where
  carrier := {a | ∀ g, φ g a = a}
  add_mem' := by intro a b ha hb g; simp [ha g, hb g]
  zero_mem' := by intro g; simp
  mul_mem' := by intro a b ha hb g; simp [ha g, hb g]
  one_mem' := by intro g; simp
  algebraMap_mem' := by intro k g; exact (φ g).commutes k

theorem fixedSubalgebra_etale {G : Type u} [Group G] {X : CommAlgCat.FiniteEtale.{0} K}
    (φ : G → (X →ₐ[K] X)) : Algebra.Etale K (fixedSubalgebra φ) := by
  haveI : Module.Finite K X := inferInstance
  haveI : Algebra.Etale K X := inferInstance
  exact etale_subalgebra (A := X) (fixedSubalgebra φ)

theorem fixedSubalgebra_finite {G : Type u} [Group G] {X : CommAlgCat.FiniteEtale.{0} K}
    (φ : G → (X →ₐ[K] X)) : Module.Finite K (fixedSubalgebra φ) := by
  haveI : Module.Finite K X := inferInstance
  exact inferInstance

end S1746Probe

