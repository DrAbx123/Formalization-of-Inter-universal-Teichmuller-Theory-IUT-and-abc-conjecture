import LeanFormal.IUT.Foundations.AlgebraicGeometry.SplitCaseAtomCorners
import LeanFormal.IUT.Foundations.AlgebraicGeometry.M2GlobalSupport
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SplitCaseCornerFixedPoints
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SplitCaseGlobalAtoms
import Mathlib.Tactic

open scoped BigOperators

namespace SplitCaseCornerPermutation

noncomputable section

universe u

variable {S : Type u} [CommRing S] {G : Type u} [Group G] [Fintype G] [DecidableEq G]
  {n : ℕ} [MulSemiringAction G (Fin n → S)] [SMulCommClass G S (Fin n → S)]

def e (i : Fin n) : Fin n → S := Pi.single i (1 : S)

def coeff (g : G) (i j : Fin n) : S := (g • e (S := S) i) j

lemma coeff_idem (g : G) (i j : Fin n) : IsIdempotentElem (coeff (S := S) g i j) := by
  have hstd : IsIdempotentElem (e (S := S) i) := by
    rw [IsIdempotentElem]; ext j; by_cases h : j = i <;> simp [e, Pi.single, h]
  have hfun : IsIdempotentElem (g • e (S := S) i) := by
    rw [IsIdempotentElem, ← smul_mul', hstd.eq]
  have hc := congrFun hfun.eq j
  simpa [coeff, IsIdempotentElem] using hc

abbrev K (G : Type u) (n : ℕ) := G × Fin n × Fin n

def coeffFamily : K G n → S := fun p => coeff (S := S) p.1 p.2.1 p.2.2

theorem coeffFamily_idem (p : K G n) : IsIdempotentElem (coeffFamily (S := S) p) :=
  coeff_idem p.1 p.2.1 p.2.2



def eA (A : Finset (K G n)) : S :=
  SplitCaseGlobalAtoms.epsilonAtom (coeffFamily (S := S)) A

lemma eA_idem (A : Finset (K G n)) : IsIdempotentElem (eA (S := S) A) :=
  SplitCaseGlobalAtoms.epsilonAtom_idempotent (coeffFamily (S := S)) (coeffFamily_idem (S := S)) A

abbrev I (A : Finset (K G n)) : Ideal S := Ideal.span ({1 - eA (S := S) A} : Set S)

abbrev SA (A : Finset (K G n)) : Type u := S ⧸ I (S := S) A

def M (A : Finset (K G n)) (g : G) (i j : Fin n) : SA (S := S) A :=
  Ideal.Quotient.mk (I (S := S) A) (coeff (S := S) g i j)

lemma h01 (A : Finset (K G n)) (g : G) (i j : Fin n) :
    M (S := S) A g i j = 0 ∨ M (S := S) A g i j = 1 :=
  SplitCaseAtomCorners.coeff_eq_zero_or_one_on_corner (a := coeffFamily (S := S))
    (coeffFamily_idem (S := S)) A (g, i, j)


open Classical in
noncomputable def cornerMap (A : Finset (K G n)) :
    (Fin n → S) →ₐ[S] (Fin n → SA (S := S) A) where
  toFun x j := Ideal.Quotient.mk (I (S := S) A) (x j)
  map_one' := by ext j; simp
  map_mul' x y := by ext j; simp
  map_zero' := by ext j; simp
  map_add' x y := by ext j; simp
  commutes' s := by ext j; simp

lemma cornerMap_surjective (A : Finset (K G n)) :
    Function.Surjective (cornerMap (S := S) A) := by
  intro y
  choose x hx using fun j => Ideal.Quotient.mk_surjective (I := I (S := S) A) (y j)
  exact ⟨x, by ext j; exact hx j⟩

noncomputable def cornerEquiv (A : Finset (K G n)) :
    (Fin n → S) ⧸ RingHom.ker ((cornerMap (S := S) A).toRingHom) ≃+*
      (Fin n → SA (S := S) A) :=
  RingHom.quotientKerEquivOfSurjective
    (f := (cornerMap (S := S) A).toRingHom)
    (by simpa using cornerMap_surjective (S := S) A)

lemma eA_fixed (A : Finset (K G n)) (g : G) :
    g • algebraMap S (Fin n → S) (eA (S := S) A) =
      algebraMap S (Fin n → S) (eA (S := S) A) := by
  simp

lemma mk_eq_zero_imp_eA_mul (A : Finset (K G n)) {x : S}
    (hx : Ideal.Quotient.mk (I (S := S) A) x = 0) : eA (S := S) A * x = 0 := by
  have hmem : x ∈ I (S := S) A := Ideal.Quotient.eq_zero_iff_mem.mp hx
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmem
  calc eA (S := S) A * x = eA (S := S) A * (y * (1 - eA (S := S) A)) := by rw [hy]
    _ = (eA (S := S) A * (1 - eA (S := S) A)) * y := by ring
    _ = 0 := by rw [(eA_idem (S := S) A).mul_one_sub_self, zero_mul]

lemma coeff_mem_I_of_mk_eq_zero (A : Finset (K G n)) {g : G} {i j : Fin n}
    (h : M (S := S) A g i j = 0) :
    coeff (S := S) g i j ∈ I (S := S) A :=
  Ideal.Quotient.eq_zero_iff_mem.mp h


abbrev J (A : Finset (K G n)) : Ideal (Fin n → S) :=
  RingHom.ker ((cornerMap (S := S) A).toRingHom)

lemma g_mem_J (A : Finset (K G n)) (g : G) {x : Fin n → S} (hx : x ∈ J (S := S) A) :
    g • x ∈ J (S := S) A := by
  rw [J, RingHom.mem_ker] at hx ⊢
  ext j
  have hxj : Ideal.Quotient.mk (Ideal.span ({1 - eA (S := S) A} : Set S)) (x j) = 0 := by
    simpa [cornerMap, I] using congrFun hx j
  have hmem : x j ∈ I (S := S) A := Ideal.Quotient.eq_zero_iff_mem.mp hxj
  let y : Fin n → S := fun k => Classical.choose (Ideal.mem_span_singleton'.mp
    (Ideal.Quotient.eq_zero_iff_mem.mp (by
      have := congrFun hx k
      simpa [cornerMap] using this)))
  have hy : ∀ k, y k * (1 - eA (S := S) A) = x k := by
    intro k
    exact Classical.choose_spec (Ideal.mem_span_singleton'.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp (by
        have := congrFun hx k
        simpa [cornerMap] using this)))
  have hxdecomp : x = algebraMap S (Fin n → S) (1 - eA (S := S) A) * y := by
    ext k
    change x k = (1 - eA (S := S) A) * y k
    rw [← hy k, mul_comm]
  have hgsmul : g • x = algebraMap S (Fin n → S) (1 - eA (S := S) A) * (g • y) := by
    rw [hxdecomp, smul_mul', smul_algebraMap]
  have hcoord : (g • x) j = (g • y) j * (1 - eA (S := S) A) := by
    rw [hgsmul]
    change (1 - eA (S := S) A) * (g • y) j = (g • y) j * (1 - eA (S := S) A)
    ring
  change Ideal.Quotient.mk (Ideal.span ({1 - eA (S := S) A} : Set S))
      ((g • x) j) = 0
  rw [hcoord]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton'.mpr ⟨(g • y) j, rfl⟩)



noncomputable def cornerActionHom (A : Finset (K G n)) (g : G) :
    (Fin n → S) ⧸ J (S := S) A →+* (Fin n → S) ⧸ J (S := S) A :=
  Ideal.Quotient.lift (J (S := S) A)
    ((Ideal.Quotient.mk (J (S := S) A)).comp
      (MulSemiringAction.toRingEquiv G (Fin n → S) g).toRingHom)
    (fun x hx => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact g_mem_J (S := S) A g hx)

@[simp] lemma cornerActionHom_mk (A : Finset (K G n)) (g : G) (x : Fin n → S) :
    cornerActionHom (S := S) A g (Ideal.Quotient.mk (J (S := S) A) x) =
      Ideal.Quotient.mk (J (S := S) A) (g • x) := rfl

noncomputable def cornerActionRingEquiv (A : Finset (K G n)) (g : G) :
    (Fin n → S) ⧸ J (S := S) A ≃+* (Fin n → S) ⧸ J (S := S) A where
  toFun := cornerActionHom (S := S) A g
  invFun := cornerActionHom (S := S) A g⁻¹
  left_inv x := by
    have h : (cornerActionHom (S := S) A g⁻¹).comp (cornerActionHom (S := S) A g) =
        RingHom.id ((Fin n → S) ⧸ J (S := S) A) := by
      apply Ideal.Quotient.ringHom_ext
      ext y
      simp [cornerActionHom_mk, ← mul_smul]
    exact congrFun (congrArg DFunLike.coe h) x
  right_inv x := by
    have h : (cornerActionHom (S := S) A g).comp (cornerActionHom (S := S) A g⁻¹) =
        RingHom.id ((Fin n → S) ⧸ J (S := S) A) := by
      apply Ideal.Quotient.ringHom_ext
      ext y
      simp [cornerActionHom_mk, ← mul_smul]
    exact congrFun (congrArg DFunLike.coe h) x
  map_mul' x y := map_mul (cornerActionHom (S := S) A g) x y
  map_add' x y := map_add (cornerActionHom (S := S) A g) x y




@[simp] lemma cornerEquiv_apply_mk (A : Finset (K G n)) (x : Fin n → S) :
    cornerEquiv (S := S) A (Ideal.Quotient.mk (J (S := S) A) x) =
      cornerMap (S := S) A x :=
  RingHom.quotientKerEquivOfSurjective_apply_mk _ x

@[simp] lemma cornerEquiv_symm_cornerMap (A : Finset (K G n)) (x : Fin n → S) :
    (cornerEquiv (S := S) A).symm (cornerMap (S := S) A x) =
      Ideal.Quotient.mk (J (S := S) A) x :=
  RingHom.quotientKerEquivOfSurjective_symm_apply _ x

noncomputable def cornerSigmaRingEquiv (A : Finset (K G n)) (g : G) :
    (Fin n → SA (S := S) A) ≃+* (Fin n → SA (S := S) A) :=
  (cornerEquiv (S := S) A).symm.trans
    ((cornerActionRingEquiv (S := S) A g).trans (cornerEquiv (S := S) A))


noncomputable def cornerSigma (A : Finset (K G n)) (g : G) :
    (Fin n → SA (S := S) A) ≃ₐ[SA (S := S) A] (Fin n → SA (S := S) A) :=
  AlgEquiv.ofRingEquiv (f := cornerSigmaRingEquiv (S := S) A g) (fun s => by
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective (I := I (S := S) A) s
    rw [show (algebraMap (SA (S := S) A) (Fin n → SA (S := S) A)
        (Ideal.Quotient.mk (I (S := S) A) t)) =
        cornerMap (S := S) A (algebraMap S (Fin n → S) t) by
      ext j
      simp [cornerMap]]
    rw [cornerSigmaRingEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply,
      cornerEquiv_symm_cornerMap]
    rw [show cornerActionRingEquiv (S := S) A g
        (Ideal.Quotient.mk (J (S := S) A) (algebraMap S (Fin n → S) t)) =
        Ideal.Quotient.mk (J (S := S) A) (algebraMap S (Fin n → S) t) by
      change cornerActionHom (S := S) A g
        (Ideal.Quotient.mk (J (S := S) A) (algebraMap S (Fin n → S) t)) = _
      rw [cornerActionHom_mk, smul_algebraMap]]
    rw [cornerEquiv_apply_mk])



lemma cornerSigma_single (A : Finset (K G n)) (g : G) (i : Fin n) :
    cornerSigma (S := S) A g (Pi.single i (1 : SA (S := S) A)) =
      fun j => M (S := S) A g i j := by
  ext j
  rw [show (Pi.single i (1 : SA (S := S) A)) =
      cornerMap (S := S) A (Pi.single i (1 : S)) by
    ext k; by_cases h : k = i <;> simp [cornerMap, Pi.single, h]]
  change cornerSigmaRingEquiv (S := S) A g
    (cornerMap (S := S) A (Pi.single i (1 : S))) j = M (S := S) A g i j
  rw [cornerSigmaRingEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply,
    cornerEquiv_symm_cornerMap]
  change cornerEquiv (S := S) A
    (cornerActionHom (S := S) A g
      (Ideal.Quotient.mk (J (S := S) A) (Pi.single i (1 : S)))) j = _
  rw [cornerActionHom_mk, cornerEquiv_apply_mk]
  rfl

lemma cornerSigma_h01 (A : Finset (K G n)) (g : G) (i j : Fin n) :
    cornerSigma (S := S) A g (Pi.single i (1 : SA (S := S) A)) j = 0 ∨
      cornerSigma (S := S) A g (Pi.single i (1 : SA (S := S) A)) j = 1 := by
  rw [cornerSigma_single]
  exact h01 (S := S) A g i j


lemma eA_eq_zero_of_one_mem_I (A : Finset (K G n))
    (h1 : (1 : S) ∈ I (S := S) A) : eA (S := S) A = 0 := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp h1
  calc eA (S := S) A = eA (S := S) A * 1 := (mul_one _).symm
    _ = eA (S := S) A * (y * (1 - eA (S := S) A)) := by rw [hy]
    _ = (eA (S := S) A * (1 - eA (S := S) A)) * y := by ring
    _ = 0 := by rw [(eA_idem (S := S) A).mul_one_sub_self, zero_mul]

lemma nontrivial_SA_of_ne_zero (A : Finset (K G n)) (hA : eA (S := S) A ≠ 0) :
    Nontrivial (SA (S := S) A) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have hmem : (1 : S) ∈ I (S := S) A :=
    Ideal.Quotient.eq_zero_iff_mem.mp h.symm
  exact hA (eA_eq_zero_of_one_mem_I (S := S) A hmem)

noncomputable def cornerPermutation (A : Finset (K G n)) (hA : eA (S := S) A ≠ 0) (g : G) : Equiv.Perm (Fin n) := by
  classical
  letI : DecidableEq (SA (S := S) A) := Classical.decEq _
  letI : Nontrivial (SA (S := S) A) := nontrivial_SA_of_ne_zero (S := S) A hA
  exact Classical.choose (ABCBridge.M2GlobalSupport.perm_of_coeff_zero_one
    (S := SA (S := S) A) (cornerSigma (S := S) A g) (cornerSigma_h01 (S := S) A g))

lemma cornerPermutation_spec (A : Finset (K G n)) (hA : eA (S := S) A ≠ 0) (g : G) (i : Fin n) :
    cornerSigma (S := S) A g (Pi.single i (1 : SA (S := S) A)) =
      Pi.single (cornerPermutation (S := S) A hA g i) (1 : SA (S := S) A) := by
  classical
  letI : DecidableEq (SA (S := S) A) := Classical.decEq _
  letI : Nontrivial (SA (S := S) A) := nontrivial_SA_of_ne_zero (S := S) A hA
  exact Classical.choose_spec (ABCBridge.M2GlobalSupport.perm_of_coeff_zero_one
    (S := SA (S := S) A) (cornerSigma (S := S) A g) (cornerSigma_h01 (S := S) A g)) i



lemma cornerSigma_cornerMap (A : Finset (K G n)) (g : G) (x : Fin n → S) :
    cornerSigma (S := S) A g (cornerMap (S := S) A x) =
      cornerMap (S := S) A (g • x) := by
  change cornerSigmaRingEquiv (S := S) A g (cornerMap (S := S) A x) = _
  rw [cornerSigmaRingEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply,
    cornerEquiv_symm_cornerMap]
  change cornerEquiv (S := S) A
    (cornerActionHom (S := S) A g (Ideal.Quotient.mk (J (S := S) A) x)) = _
  rw [cornerActionHom_mk, cornerEquiv_apply_mk]

lemma cornerSigma_comp (A : Finset (K G n)) (g h : G) :
    (cornerSigma (S := S) A h).trans (cornerSigma (S := S) A g) =
      cornerSigma (S := S) A (g * h) := by
  ext x
  obtain ⟨x0, rfl⟩ := cornerMap_surjective (S := S) A x
  simp [cornerSigma_cornerMap, mul_smul]

lemma cornerSigma_one (A : Finset (K G n)) :
    cornerSigma (S := S) A (1 : G) =
      (AlgEquiv.refl : (Fin n → SA (S := S) A) ≃ₐ[SA (S := S) A] (Fin n → SA (S := S) A)) := by
  ext x
  obtain ⟨x0, rfl⟩ := cornerMap_surjective (S := S) A x
  simp [cornerSigma_cornerMap]

lemma pi_single_inj_SA (A : Finset (K G n)) (hA : eA (S := S) A ≠ 0)
    {a b : Fin n}
    (h : (Pi.single a (1 : SA (S := S) A) : Fin n → SA (S := S) A) =
      (Pi.single b (1 : SA (S := S) A) : Fin n → SA (S := S) A)) : a = b := by
  classical
  letI : Nontrivial (SA (S := S) A) := nontrivial_SA_of_ne_zero (S := S) A hA
  by_contra hab
  have hcoord := congrFun h a
  simpa [Pi.single, hab] using hcoord

lemma cornerPermutation_mul_apply (A : Finset (K G n)) (hA : eA (S := S) A ≠ 0)
    (g h : G) (i : Fin n) :
    cornerPermutation (S := S) A hA (g * h) i =
      cornerPermutation (S := S) A hA g (cornerPermutation (S := S) A hA h i) := by
  apply pi_single_inj_SA (S := S) A hA
  calc
    Pi.single (cornerPermutation (S := S) A hA (g * h) i) (1 : SA (S := S) A)
        = cornerSigma (S := S) A (g * h) (Pi.single i (1 : SA (S := S) A)) :=
          (cornerPermutation_spec (S := S) A hA (g * h) i).symm
    _ = cornerSigma (S := S) A g
          (cornerSigma (S := S) A h (Pi.single i (1 : SA (S := S) A))) := by
          rw [← cornerSigma_comp (S := S) A g h]
          rfl
    _ = cornerSigma (S := S) A g
          (Pi.single (cornerPermutation (S := S) A hA h i) (1 : SA (S := S) A)) := by
          rw [cornerPermutation_spec (S := S) A hA h i]
    _ = Pi.single (cornerPermutation (S := S) A hA g
          (cornerPermutation (S := S) A hA h i)) (1 : SA (S := S) A) :=
          cornerPermutation_spec (S := S) A hA g (cornerPermutation (S := S) A hA h i)

lemma cornerPermutation_one_apply (A : Finset (K G n)) (hA : eA (S := S) A ≠ 0)
    (i : Fin n) : cornerPermutation (S := S) A hA 1 i = i := by
  apply (pi_single_inj_SA (S := S) A hA)
  have hspec := cornerPermutation_spec (S := S) A hA 1 i
  rw [cornerSigma_one] at hspec
  exact hspec.symm

noncomputable def cornerPermutationHom (A : Finset (K G n))
    (hA : eA (S := S) A ≠ 0) : G →* Equiv.Perm (Fin n) where
  toFun := cornerPermutation (S := S) A hA
  map_one' := by
    ext i
    exact congrArg Fin.val (cornerPermutation_one_apply (S := S) A hA i)
  map_mul' g h := by
    ext i
    exact congrArg Fin.val (by
      simpa [Equiv.Perm.mul_apply] using cornerPermutation_mul_apply (S := S) A hA g h i)



lemma pi_eq_sum_single {R : Type u} [Semiring R] {m : ℕ} (x : Fin m → R) :
    x = ∑ j : Fin m, x j • (Pi.single j (1 : R) : Fin m → R) := by
  ext k
  rw [Finset.sum_apply, Finset.sum_eq_single k]
  · simp [Pi.single, Pi.smul_apply]
  · intro j hj hjk
    have hkj : k ≠ j := Ne.symm hjk
    simp [Pi.single, Pi.smul_apply, Function.update, hkj]
  · intro hk
    simp at hk


lemma permAction_single (A : Finset (K G n)) (hA : eA (S := S) A ≠ 0)
    (g : G) (i : Fin n) :
    letI : MulAction G (Fin n) :=
      MulAction.compHom (Fin n) (cornerPermutationHom (S := S) A hA)
    letI : MulSemiringAction G (Fin n → SA (S := S) A) :=
      ABCBridge.SplitCaseCornerFixedPoints.finFunctionMulSemiringAction
        (R := SA (S := S) A) (G := G)
        (ρ := cornerPermutationHom (S := S) A hA)
    letI : SMulCommClass G (SA (S := S) A) (Fin n → SA (S := S) A) :=
      ABCBridge.SplitCaseCornerFixedPoints.finFunctionSMulCommClass
        (R := SA (S := S) A) (G := G)
        (ρ := cornerPermutationHom (S := S) A hA)
    (MulSemiringAction.toAlgEquiv (SA (S := S) A) (Fin n → SA (S := S) A) g)
        (Pi.single i (1 : SA (S := S) A)) =
      Pi.single (cornerPermutation (S := S) A hA g i) (1 : SA (S := S) A) := by
  letI : MulAction G (Fin n) :=
    MulAction.compHom (Fin n) (cornerPermutationHom (S := S) A hA)
  letI : MulSemiringAction G (Fin n → SA (S := S) A) :=
    ABCBridge.SplitCaseCornerFixedPoints.finFunctionMulSemiringAction
      (R := SA (S := S) A) (G := G)
      (ρ := cornerPermutationHom (S := S) A hA)
  letI : SMulCommClass G (SA (S := S) A) (Fin n → SA (S := S) A) :=
    ABCBridge.SplitCaseCornerFixedPoints.finFunctionSMulCommClass
      (R := SA (S := S) A) (G := G)
      (ρ := cornerPermutationHom (S := S) A hA)
  ext k
  change (Pi.single i (1 : SA (S := S) A) : Fin n → SA (S := S) A)
      ((cornerPermutationHom (S := S) A hA g)⁻¹ k) =
    (Pi.single (cornerPermutation (S := S) A hA g i) (1 : SA (S := S) A) : Fin n → SA (S := S) A) k
  by_cases h : k = cornerPermutation (S := S) A hA g i
  · subst h
    have hinv : (cornerPermutationHom (S := S) A hA g)⁻¹
        (cornerPermutation (S := S) A hA g i) = i := by
      simp [cornerPermutationHom]
    simp [Pi.single, hinv]
  · have hne : (cornerPermutationHom (S := S) A hA g)⁻¹ k ≠ i := by
      intro hEq
      apply h
      calc k = cornerPermutation (S := S) A hA g
            ((cornerPermutationHom (S := S) A hA g)⁻¹ k) := by
              simp [cornerPermutationHom]
        _ = cornerPermutation (S := S) A hA g i := by rw [hEq]
    have hne' : (Equiv.symm ((cornerPermutationHom (S := S) A hA) g)) k ≠ i := by
      simpa using hne
    simp [Pi.single, h, hne', Function.update]

lemma cornerSigma_eq_toAlgEquiv (A : Finset (K G n)) (hA : eA (S := S) A ≠ 0)
    (g : G) :
    letI : MulAction G (Fin n) :=
      MulAction.compHom (Fin n) (cornerPermutationHom (S := S) A hA)
    letI : MulSemiringAction G (Fin n → SA (S := S) A) :=
      ABCBridge.SplitCaseCornerFixedPoints.finFunctionMulSemiringAction
        (R := SA (S := S) A) (G := G)
        (ρ := cornerPermutationHom (S := S) A hA)
    letI : SMulCommClass G (SA (S := S) A) (Fin n → SA (S := S) A) :=
      ABCBridge.SplitCaseCornerFixedPoints.finFunctionSMulCommClass
        (R := SA (S := S) A) (G := G)
        (ρ := cornerPermutationHom (S := S) A hA)
    cornerSigma (S := S) A g =
      MulSemiringAction.toAlgEquiv (SA (S := S) A) (Fin n → SA (S := S) A) g := by
  letI : MulAction G (Fin n) :=
    MulAction.compHom (Fin n) (cornerPermutationHom (S := S) A hA)
  letI : MulSemiringAction G (Fin n → SA (S := S) A) :=
    ABCBridge.SplitCaseCornerFixedPoints.finFunctionMulSemiringAction
      (R := SA (S := S) A) (G := G)
      (ρ := cornerPermutationHom (S := S) A hA)
  letI : SMulCommClass G (SA (S := S) A) (Fin n → SA (S := S) A) :=
    ABCBridge.SplitCaseCornerFixedPoints.finFunctionSMulCommClass
      (R := SA (S := S) A) (G := G)
      (ρ := cornerPermutationHom (S := S) A hA)
  apply AlgEquiv.ext
  intro x
  rw [pi_eq_sum_single x]
  simp only [map_sum, map_smul]
  congr 1 with i
  rw [cornerPermutation_spec (S := S) A hA g i]
  rw [permAction_single (S := S) A hA g i]



end
end SplitCaseCornerPermutation

