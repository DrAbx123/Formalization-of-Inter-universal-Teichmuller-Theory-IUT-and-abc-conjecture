
/-- A K-subalgebra of a finite etale K-algebra is etale over K.

This is Galois descent for etaleness: base change to an algebraic closure and use
that a subalgebra of a finite power of a separably closed field is split. -/
theorem etale_subalgebra {A : Type v} [CommRing A] [Algebra K A]
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
      Module.Flat.lTensor_preserves_injective_linearMap (M := Kbar) B.val.toLinearMap
        Subtype.val_injective
    exact hlin h
  haveI : Algebra.IsFiniteSplit Kbar (Kbar ⊗[K] A) := inferInstance
  obtain ⟨n, ⟨eA⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun Kbar (Kbar ⊗[K] A)
  let f : Kbar ⊗[K] B →ₐ[Kbar] (Fin n → Kbar) := eA.toAlgHom.comp i
  have hf : Function.Injective f := eA.injective.comp hi
  haveI : Algebra.IsFiniteSplit Kbar (Kbar ⊗[K] B) :=
    finiteSplit_of_injective_pi (K := Kbar) (R := Kbar ⊗[K] B) (ι := Fin n) f hf
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat (R := K) (S := B) Kbar

end EtaleSubalgebra

/-! ## 2. The invariant subalgebra -/

section FixedPoints

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A]

/-- The subalgebra of A fixed by a family of K-algebra endomorphisms indexed by G.

Only the algebra-homomorphism property of the maps is used, so this makes sense for any
family; the group law is irrelevant for the definition (and for etaleness), and enters
only through the categorical limit statement in Section 3. -/
def fixedSubalgebra (G : Type u) [Group G] (φ : G → (A →ₐ[K] A)) : Subalgebra K A where
  carrier := {a | ∀ g, φ g a = a}
  add_mem' := by intro a b ha hb g; simp [ha g, hb g]
  zero_mem' := by intro g; simp
  mul_mem' := by intro a b ha hb g; simp [ha g, hb g]
  one_mem' := by intro g; simp
  algebraMap_mem' := by intro k g; exact (φ g).commutes k

/-- Universal property of the fixed point subalgebra: any K-algebra map from a
K-algebra B into A whose image is fixed by G factors uniquely through A^G. -/
theorem existsUnique_lift_fixedSubalgebra {G : Type u} [Group G] (φ : G → (A →ₐ[K] A))
    {B : Type u} [CommRing B] [Algebra K B] (f : B →ₐ[K] A)
    (hf : ∀ (b : B) (g : G), φ g (f b) = f b) :
    ∃! F : B →ₐ[K] ↥(fixedSubalgebra G φ),
      (Subalgebra.val (fixedSubalgebra G φ)).comp F = f := by
  refine ⟨AlgHom.codRestrict f (fixedSubalgebra G φ) (fun b g => hf b g), ?_, ?_⟩
  · ext b
    rfl
  · intro F hF
    ext b
    have h := congrArg (fun (g : B →ₐ[K] A) => g b) hF
    simpa using h

end FixedPoints