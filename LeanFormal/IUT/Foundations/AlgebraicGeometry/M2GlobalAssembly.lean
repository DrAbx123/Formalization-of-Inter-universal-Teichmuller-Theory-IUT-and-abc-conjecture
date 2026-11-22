import LeanFormal.IUT.Foundations.AlgebraicGeometry.SplitCaseGlobalCoefficients
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SplitCaseCornerPermutation
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SplitCaseProductSubsingleton
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SplitCaseFixedPointsTransport
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SplitCasePiFixedPoints
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SplitCaseCornerFixedPoints
import LeanFormal.IUT.Foundations.AlgebraicGeometry.M2BaseTransport
import LeanFormal.IUT.Foundations.AlgebraicGeometry.CRTEquivariance
import LeanFormal.IUT.Foundations.AlgebraicGeometry.M2FixedPointProduct
import LeanFormal.IUT.Foundations.AlgebraicGeometry.CornerEtaleComp
import LeanFormal.IUT.Foundations.AlgebraicGeometry.IdempotentQuotientEtale
import LeanFormal.IUT.Foundations.AlgebraicGeometry.M2BaseTransport
import Mathlib.Tactic

set_option maxHeartbeats 3000000
open scoped BigOperators

namespace M2FinalAssembly

universe u
variable {S : Type u} [CommRing S] {G : Type u} [Group G] [Fintype G] [DecidableEq G]
  {n : ℕ} [MulSemiringAction G (Fin n → S)] [SMulCommClass G S (Fin n → S)]

abbrev CoeffIdx (G : Type u) (n : ℕ) := G × Fin n × Fin n

abbrev eA (A : Finset (CoeffIdx G n)) : S := SplitCaseCornerPermutation.eA (S := S) A

abbrev SA (A : Finset (CoeffIdx G n)) : Type u := SplitCaseCornerPermutation.SA (S := S) A

noncomputable def snz (S : Type u) [CommRing S] (G : Type u) [Group G] [Fintype G] [DecidableEq G] (n : ℕ) [MulSemiringAction G (Fin n → S)] [SMulCommClass G S (Fin n → S)] : Finset (Finset (CoeffIdx G n)) := by
  classical
  exact Finset.univ.filter (fun A => SplitCaseCornerPermutation.eA (S := S) A ≠ 0)

abbrev κ (S : Type u) [CommRing S] (G : Type u) [Group G] [Fintype G] [DecidableEq G] (n : ℕ) [MulSemiringAction G (Fin n → S)] [SMulCommClass G S (Fin n → S)] : Type u := {A : Finset (CoeffIdx G n) // A ∈ snz S G n}

lemma subsingleton_SA_of_not_mem {A : Finset (CoeffIdx G n)}
    (hA : A ∉ snz S G n) :
    Subsingleton (SA (S := S) A) := by
  classical
  have hzero : eA (S := S) A = 0 := by
    by_contra h
    exact hA (Finset.mem_filter.mpr ⟨Finset.mem_univ A, h⟩)
  have hI : SplitCaseCornerPermutation.I (S := S) A = ⊤ := by
    change Ideal.span ({1 - SplitCaseCornerPermutation.eA (S := S) A} : Set S) = ⊤
    simp [SplitCaseCornerPermutation.I, hzero]
  change Subsingleton (S ⧸ SplitCaseCornerPermutation.I (S := S) A)
  rw [hI]
  infer_instance

noncomputable def Sprod :
    S ≃+* ((A : κ S G n) → SA (S := S) A.1) :=
  ABCBridge.SplitCaseProductSubsingleton.dropSubsingletonFactors
    (S := S) (Rc := fun A => SA (S := S) A)
    (snz S G n)
    (fun A hA => subsingleton_SA_of_not_mem (S := S) (G := G) (n := n) hA)
    (SplitCaseGlobalCoefficients.productEquiv (S := S) (G := G) (n := n))


lemma productEquiv_apply (x : S) (A : Finset (CoeffIdx G n)) :
    SplitCaseGlobalCoefficients.productEquiv (S := S) (G := G) (n := n) x A =
      Ideal.Quotient.mk (SplitCaseCornerPermutation.I (S := S) A) x := rfl

lemma Sprod_apply (x : S) (A : κ S G n) :
    Sprod (S := S) (G := G) (n := n) x A =
      SplitCaseGlobalCoefficients.productEquiv (S := S) (G := G) (n := n) x A.1 := by
  rfl

noncomputable def crtMap :
    (Fin n → S) →+* ((A : κ S G n) → (Fin n → SA (S := S) A.1)) where
  toFun x A j := Ideal.Quotient.mk (SplitCaseCornerPermutation.I (S := S) A.1) (x j)
  map_one' := by ext A j; simp
  map_mul' x y := by ext A j; simp
  map_add' x y := by ext A j; simp
  map_zero' := by ext A j; simp

lemma crtMap_apply (x : Fin n → S) (A : κ S G n) (j : Fin n) :
    crtMap (S := S) (G := G) (n := n) x A j =
      Ideal.Quotient.mk (SplitCaseCornerPermutation.I (S := S) A.1) (x j) := rfl

lemma crtMap_surjective : Function.Surjective (crtMap (S := S) (G := G) (n := n)) := by
  intro y
  choose x hx using fun j =>
    (Sprod (S := S) (G := G) (n := n)).surjective (fun A => y A j)
  refine ⟨x, ?_⟩
  ext A j
  rw [crtMap_apply]
  change Ideal.Quotient.mk (SplitCaseCornerPermutation.I (S := S) A.1) (x j) = y A j
  rw [← congrFun (hx j) A]
  rw [Sprod_apply, productEquiv_apply]

lemma crtMap_injective : Function.Injective (crtMap (S := S) (G := G) (n := n)) := by
  intro x y h
  funext j
  apply (Sprod (S := S) (G := G) (n := n)).injective
  funext A
  have := congrFun (congrFun h A) j
  simpa [crtMap_apply, Sprod_apply, productEquiv_apply] using this

noncomputable def crtEquiv :
    (Fin n → S) ≃+* ((A : κ S G n) → (Fin n → SA (S := S) A.1)) :=
  RingEquiv.ofBijective (crtMap (S := S) (G := G) (n := n))
    ⟨crtMap_injective (S := S) (G := G) (n := n),
     crtMap_surjective (S := S) (G := G) (n := n)⟩


lemma crtMap_algebraMap (s : S) :
    crtMap (S := S) (G := G) (n := n) (algebraMap S (Fin n → S) s) =
      algebraMap S ((A : κ S G n) → (Fin n → SA (S := S) A.1)) s := by
  ext A j
  simp [crtMap_apply]

noncomputable def crtAlgEquiv :
    (Fin n → S) ≃ₐ[S] ((A : κ S G n) → (Fin n → SA (S := S) A.1)) :=
  AlgEquiv.ofRingEquiv (f := crtEquiv (S := S) (G := G) (n := n))
    (fun s => by
      change crtMap (S := S) (G := G) (n := n) (algebraMap S (Fin n → S) s) =
        algebraMap S ((A : κ S G n) → (Fin n → SA (S := S) A.1)) s
      exact crtMap_algebraMap (S := S) (G := G) (n := n) s)




lemma mem_snz_iff {A : Finset (CoeffIdx G n)} :
    A ∈ snz S G n ↔ eA (S := S) A ≠ 0 := by
  classical
  simp [snz]

noncomputable def rho (A : κ S G n) : G →* Equiv.Perm (Fin n) := by
  classical
  exact SplitCaseCornerPermutation.cornerPermutationHom (S := S) A.1
    ((mem_snz_iff (S := S) (G := G) (n := n)).mp A.2)

noncomputable local instance cornerActionInst (A : κ S G n) :
    MulSemiringAction G (Fin n → SA (S := S) A.1) :=
  ABCBridge.SplitCaseCornerFixedPoints.finFunctionMulSemiringAction
    (R := SA (S := S) A.1) (G := G) (ρ := rho (S := S) A)

noncomputable local instance cornerSMulSAInst (A : κ S G n) :
    SMulCommClass G (SA (S := S) A.1) (Fin n → SA (S := S) A.1) :=
  ABCBridge.SplitCaseCornerFixedPoints.finFunctionSMulCommClass
    (R := SA (S := S) A.1) (G := G) (ρ := rho (S := S) A)

noncomputable local instance cornerSMulSInst (A : κ S G n) :
    SMulCommClass G S (Fin n → SA (S := S) A.1) :=
  ⟨fun g s f => by
    letI := cornerActionInst (S := S) A
    funext j
    rfl⟩

noncomputable local instance piActionInst :
    MulSemiringAction G ((A : κ S G n) → (Fin n → SA (S := S) A.1)) :=
  ABCBridge.SplitCasePiFixedPoints.piMulSemiringAction
    (T := fun A : κ S G n => Fin n → SA (S := S) A.1)

noncomputable local instance piSMulInst :
    SMulCommClass G S ((A : κ S G n) → (Fin n → SA (S := S) A.1)) :=
  ABCBridge.SplitCasePiFixedPoints.piSMulCommClass
    (T := fun A : κ S G n => Fin n → SA (S := S) A.1)

lemma crtAlgEquiv_smul (g : G) (x : Fin n → S) :
    crtAlgEquiv (S := S) (G := G) (n := n) (g • x) =
      g • crtAlgEquiv (S := S) (G := G) (n := n) x := by
  ext A j
  change crtMap (S := S) (G := G) (n := n) (g • x) A j =
    (g • crtMap (S := S) (G := G) (n := n) x) A j
  rw [crtMap_apply]
  have h := congrFun (congrFun
    (CRTEquivariance.crtEquivariance (S := S) (G := G) (n := n) x g) A.1) j
  rw [h]
  letI := cornerActionInst (S := S) A
  change SplitCaseCornerPermutation.cornerSigma (S := S) A.1 g
      (fun k => Ideal.Quotient.mk (SplitCaseCornerPermutation.I (S := S) A.1) (x k)) j =
    (g • (fun j => Ideal.Quotient.mk (SplitCaseCornerPermutation.I (S := S) A.1) (x j))) j
  rw [CRTEquivariance.cornerSigma_apply_eq_permAction (S := S) A.1
    ((mem_snz_iff (S := S) (G := G) (n := n)).mp A.2) g]
  rfl

noncomputable def fixedProduct :
    FixedPoints.subalgebra S (Fin n → S) G ≃ₐ[S]
      ((A : κ S G n) → FixedPoints.subalgebra S (Fin n → SA (S := S) A.1) G) :=
  ABCBridge.M2FixedPointProduct.fixedPointProductAlgEquiv
    (T := fun A : κ S G n => Fin n → SA (S := S) A.1)
    (crtAlgEquiv (S := S) (G := G) (n := n))
    (crtAlgEquiv_smul (S := S) (G := G) (n := n))

lemma cornerFactor_finiteEtale (A : κ S G n) :
    Algebra.Etale S (FixedPoints.subalgebra S (Fin n → SA (S := S) A.1) G) ∧
      Module.Finite S (FixedPoints.subalgebra S (Fin n → SA (S := S) A.1) G) := by
  letI := cornerActionInst (S := S) A
  letI := cornerSMulSAInst (S := S) A
  letI := cornerSMulSInst (S := S) A
  have hc := ABCBridge.SplitCaseCornerFixedPoints.cornerFixedPoints_finiteEtaleAt
    (κ := κ S G n) (Rc := fun A => SA (S := S) A.1)
    (ρ := fun A => rho (S := S) A) A
  have hSAe : Algebra.Etale S (SA (S := S) A.1) :=
    IdempotentQuotientEtale.etale (S := S) (e := eA (S := S) A.1)
      (SplitCaseCornerPermutation.eA_idem (S := S) A.1)
  have hSAf : Module.Finite S (SA (S := S) A.1) :=
    IdempotentQuotientEtale.moduleFinite (S := S) (e := eA (S := S) A.1)
  exact ABCBridge.M2BaseTransport.fixedPoints_restrictScalars_finiteEtale
    (S := S) (R := SA (S := S) A.1) (A := Fin n → SA (S := S) A.1) (G := G)
    (hEt := hc.1) (hFin := hc.2)

theorem m2_final :
    Algebra.Etale S (FixedPoints.subalgebra S (Fin n → S) G) ∧
      Module.Finite S (FixedPoints.subalgebra S (Fin n → S) G) := by
  haveI : ∀ A : κ S G n,
      Algebra.Etale S (FixedPoints.subalgebra S (Fin n → SA (S := S) A.1) G) :=
    fun A => (cornerFactor_finiteEtale (S := S) (G := G) (n := n) A).1
  haveI : ∀ A : κ S G n,
      Module.Finite S (FixedPoints.subalgebra S (Fin n → SA (S := S) A.1) G) :=
    fun A => (cornerFactor_finiteEtale (S := S) (G := G) (n := n) A).2
  have hprod := ABCBridge.SplitCaseCornerFixedPoints.pi_finiteEtale
    (S := S) (κ := κ S G n)
    (T := fun A => FixedPoints.subalgebra S (Fin n → SA (S := S) A.1) G)
  refine ⟨?_, ?_⟩
  · exact Algebra.Etale.of_equiv (fixedProduct (S := S) (G := G) (n := n)).symm
  · exact Module.Finite.equiv (fixedProduct (S := S) (G := G) (n := n)).toLinearEquiv.symm

end M2FinalAssembly

