/-
S2673: the localized Dedekind--Frobenius orbit-size theorem.

Setting (S2537): A = O_{F'}, C = O_L, K = F', L = L,
  R = O_{F'}[1/10], S = O_L[1/10] (integral closure of R in L, S2537).

Main result (S2673_localized_orbitSizeMultiset_eq_factorDegrees):
for a monic f : R[X], a maximal p : Ideal R, a prime P : Ideal S over p,
with (f mod p) separable, f splitting over L and (f over K) separable,
and any arithmetic Frobenius sigma at P (IsArithFrobAt R sigma P), the
multiset of orbit sizes of sigma acting on the roots of f in L equals the
multiset of degrees of the irreducible factors of f mod p.

The proof reduces roots mod P by redRoot (S2539) and identifies the induced
permutation with the q-Frobenius permBar (S2540); the orbit sizes of permBar
are then factorDegrees by S2543/S2548.

No sorry, axiom, True/PUnit or native_decide is used.
-/
import tmp.sheaf.xif.paper.S2548ConcreteCycleTypeActual
import tmp.sheaf.xif.paper.S2543FrobeniusOrbitActual
import tmp.sheaf.xif.paper.S2532LocalizedDefinitionsActual
import tmp.sheaf.xif.paper.S2597RootSetEquivActual
import tmp.sheaf.xif.paper.S2592GenericLocalizedResidueIsoActual

noncomputable section
set_option maxHeartbeats 32000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual
open LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual

namespace LeanFormal.IUT.XiFPaper.S2673LocalizedOrbitSizeActual

attribute [local instance] Ideal.Quotient.field

abbrev R10 : Type := S2537ConcreteLocalizationActual.R
abbrev T10 : Type := S2537ConcreteLocalizationActual.S
abbrev OL : Type := S2537ConcreteLocalizationActual.C
abbrev K : Type := S2537ConcreteLocalizationActual.K
abbrev L10 : Type := S2537ConcreteLocalizationActual.L

/-! ## 1. The Galois action on the localized integral closure -/

/-- T10 is a fraction ring of L10, being a localization of O_L. -/
noncomputable instance S2673_isFractionRing_T10 : IsFractionRing T10 L10 :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (R := OL) (M := Algebra.algebraMapSubmonoid OL (Submonoid.powers (10 : A))) T10 L10

/-- R = O_{F'}[1/10] is a Dedekind domain. -/
noncomputable instance S2673_isDedekindDomain_R10 : IsDedekindDomain R10 :=
  IsLocalization.isDedekindDomain
    (A := A) (M := Submonoid.powers (10 : A))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (by norm_num : (10 : A) ≠ 0)) R10

/-- R is integrally closed. -/
noncomputable instance S2673_isIntegrallyClosed_R10 : IsIntegrallyClosed R10 :=
  inferInstance

/-- T10 is integral over R10. -/
noncomputable instance S2673_isIntegral_R10_T10 : Algebra.IsIntegral R10 T10 :=
  IsIntegralClosure.isIntegral_algebra (R := R10) (A := T10) (B := L10)

/-- R10 -> T10 is injective. -/
noncomputable instance S2673_faithfulSMul_R10_T10 : FaithfulSMul R10 T10 := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y hxy
  apply FaithfulSMul.algebraMap_injective R10 L10
  have h : (algebraMap T10 L10) (algebraMap R10 T10 x) =
      (algebraMap T10 L10) (algebraMap R10 T10 y) := congrArg _ hxy
  rwa [← IsScalarTower.algebraMap_apply R10 T10 L10,
    ← IsScalarTower.algebraMap_apply R10 T10 L10] at h

/-- The Galois group of L/K acts on the localized integral closure T10. -/
noncomputable instance S2673_instMulSemiringAction_T10 : MulSemiringAction Gal(L10/K) T10 :=
  IsIntegralClosure.MulSemiringAction R10 K L10 T10

/-- The action on T10 is R-linear. -/
noncomputable instance S2673_instSMulCommClass_T10 : SMulCommClass Gal(L10/K) R10 T10 where
  smul_comm g a b := by
    change (galRestrict R10 K L10 T10) g (a • b) = a • (galRestrict R10 K L10 T10) g b
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    exact (galRestrict R10 K L10 T10) g |>.commutes a

lemma S2673_smul_eq_galRestrict (sigma : Gal(L10/K)) (x : T10) :
    sigma • x = (galRestrict R10 K L10 T10) sigma x := rfl

lemma S2673_algebraMap_smul (sigma : Gal(L10/K)) (x : T10) :
    algebraMap T10 L10 (sigma • x) = sigma (algebraMap T10 L10 x) := by
  rw [S2673_smul_eq_galRestrict]
  exact algebraMap_galRestrict_apply R10 sigma x

/-! ## 2. Roots over the field and over the integral closure -/

/-- Membership in the root set does not change when the polynomial is mapped
along R -> K. -/
lemma S2673_mem_rootSet_map (f : R10[X]) (hmonic : f.Monic) (x : L10) :
    x ∈ (f.map (algebraMap R10 K)).rootSet L10 ↔ x ∈ f.rootSet L10 := by
  rw [Polynomial.mem_rootSet', Polynomial.mem_rootSet', Polynomial.map_map,
    Polynomial.aeval_map_algebraMap,
    IsScalarTower.algebraMap_eq R10 K L10]

/-- The two root sets (over R and over K) are canonically identified. -/
noncomputable def S2673_rootSetKEquiv (f : R10[X]) (hmonic : f.Monic) :
    (f.map (algebraMap R10 K)).rootSet L10 ≃ f.rootSet L10 :=
  Equiv.subtypeEquivRight (fun x => S2673_mem_rootSet_map f hmonic x)

@[simp] lemma S2673_rootSetKEquiv_apply_val (f : R10[X]) (hmonic : f.Monic)
    (x : (f.map (algebraMap R10 K)).rootSet L10) :
    (S2673_rootSetKEquiv f hmonic x).1 = x.1 := rfl

/-! ## 3. Equivariance of the reduction map -/

/-- toS is equivariant for the Galois actions on L and on T10. -/
lemma S2673_toS_smul (f : R10[X]) (hmonic : f.Monic) (hdeg : f.natDegree ≠ 0)
    (sigma : Gal(L10/K)) (a : f.rootSet L10) :
    S2597RootSetEquivActual.toS (R := R10) (S := T10) (L := L10) f hmonic hdeg (sigma • a) =
      sigma • (S2597RootSetEquivActual.toS (R := R10) (S := T10) (L := L10) f hmonic hdeg a) := by
  apply Subtype.ext
  apply IsIntegralClosure.algebraMap_injective T10 R10 L10
  simp only [S2597RootSetEquivActual.toS_val, Polynomial.rootSet.coe_smul,
    S2673_algebraMap_smul, AlgEquiv.smul_def]

/-- Reduction modulo P intertwines the Galois action on T10 with the
arithmetic q-Frobenius on the residue field. -/
lemma S2673_redRoot_smul (f : R10[X]) (p : Ideal R10) [hp : p.IsMaximal]
    (P : Ideal T10) [hP : P.IsPrime] [hPover : P.LiesOver p] [hPmax : P.IsMaximal]
    (hmonic : f.Monic) (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
    (hsplit : (f.map (algebraMap R10 L10)).Splits)
    [Fintype (R10 ⧸ p)] [Fintype (T10 ⧸ P)]
    (sigma : Gal(L10/K)) (H : IsArithFrobAt R10 sigma P) (a : f.rootSet T10) :
    redRoot (f := f) (p := p) (P := P) (hmonic := hmonic) (sigma • a) =
      permBar (f := f) (p := p) (P := P)
        (redRoot (f := f) (p := p) (P := P) (hmonic := hmonic) a) := by
  apply Subtype.ext
  have h1 : (sigma • a).1 = (MulSemiringAction.toAlgHom R10 T10 sigma) a.1 := by
    rw [Polynomial.rootSet.coe_smul, MulSemiringAction.toAlgHom_apply]
  have h2 : Ideal.Quotient.mk P ((MulSemiringAction.toAlgHom R10 T10 sigma) a.1) =
      a.1 ^ Nat.card (R10 ⧸ P.under R10) := H.mk_apply a.1
  calc (redRoot (f := f) (p := p) (P := P) (hmonic := hmonic) (sigma • a)).1
      = Ideal.Quotient.mk P (sigma • a).1 := rfl
    _ = Ideal.Quotient.mk P ((MulSemiringAction.toAlgHom R10 T10 sigma) a.1) := by rw [h1]
    _ = a.1 ^ Nat.card (R10 ⧸ P.under R10) := h2
    _ = a.1 ^ Nat.card (R10 ⧸ p) := by rw [hPover.over]
    _ = frobBar (p := p) (P := P) (Ideal.Quotient.mk P a.1) := rfl
    _ = (permBar (f := f) (p := p) (P := P)
        (redRoot (f := f) (p := p) (P := P) (hmonic := hmonic) a)).1 := rfl

/-! ## 4. The conjugacy between the root permutation and permBar -/

/-- The bijection between the roots of f in L and the roots of f mod p
in the residue field at P, obtained by sending a root into T10 and then
reducing modulo P. -/
noncomputable def S2673_reductionEquiv (f : R10[X]) (p : Ideal R10) [hp : p.IsMaximal]
    (P : Ideal T10) [hP : P.IsPrime] [hPover : P.LiesOver p] [hPmax : P.IsMaximal]
    (hmonic : f.Monic) (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
    (hsplit : (f.map (algebraMap R10 L10)).Splits) (hdeg : f.natDegree ≠ 0)
    (hsepK : (f.map (algebraMap R10 K)).Separable) :
    (f.map (algebraMap R10 K)).rootSet L10 ≃ (fbar f p).rootSet (T10 ⧸ P) := by
  classical
  have hsplitK : ((f.map (algebraMap R10 K)).map (algebraMap K L10)).Splits := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq R10 K L10]
    exact hsplit
  have hcardK : Fintype.card ((f.map (algebraMap R10 K)).rootSet L10) = f.natDegree := by
    rw [Polynomial.card_rootSet_eq_natDegree hsepK hsplitK,
      Polynomial.Monic.natDegree_map hmonic (algebraMap R10 K)]
  have hcardL : Fintype.card (f.rootSet L10) = f.natDegree := by
    rw [← Fintype.card_congr (S2673_rootSetKEquiv f hmonic), hcardK]
  have hcardS : Fintype.card (f.rootSet T10) = f.natDegree :=
    card_rootSet_eq (f := f) (p := p) (P := P) (hmonic := hmonic) (hsep := hsep)
      (hsplit := hsplit)
  exact (S2673_rootSetKEquiv f hmonic).trans
    ((Equiv.ofBijective _
        (S2597RootSetEquivActual.toS_bijective (R := R10) (S := T10) (L := L10)
          f hmonic hdeg hcardS hcardL)).trans
      (Equiv.ofBijective _
        (redRoot_bijective (f := f) (p := p) (P := P) (hmonic := hmonic)
          (hsep := hsep) (hsplit := hsplit))))

/-- The reduction equivalence is the composite redRoot o toS o rootSetKEquiv. -/
lemma S2673_reductionEquiv_apply (f : R10[X]) (p : Ideal R10) [hp : p.IsMaximal]
    (P : Ideal T10) [hP : P.IsPrime] [hPover : P.LiesOver p] [hPmax : P.IsMaximal]
    (hmonic : f.Monic) (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
    (hsplit : (f.map (algebraMap R10 L10)).Splits) (hdeg : f.natDegree ≠ 0)
    (hsepK : (f.map (algebraMap R10 K)).Separable)
    (x : (f.map (algebraMap R10 K)).rootSet L10) :
    S2673_reductionEquiv f p P hmonic hsep hsplit hdeg hsepK x =
      redRoot (f := f) (p := p) (P := P) (hmonic := hmonic)
        (S2597RootSetEquivActual.toS (R := R10) (S := T10) (L := L10)
          f hmonic hdeg (S2673_rootSetKEquiv f hmonic x)) := rfl

lemma S2673_rootSetKEquiv_smul (f : R10[X]) (hmonic : f.Monic) (sigma : Gal(L10/K))
    (x : (f.map (algebraMap R10 K)).rootSet L10) :
    S2673_rootSetKEquiv f hmonic (sigma • x) = sigma • (S2673_rootSetKEquiv f hmonic x) := by
  apply Subtype.ext
  simp only [S2673_rootSetKEquiv_apply_val, Polynomial.rootSet.coe_smul, AlgEquiv.smul_def]

/-- The root permutation rootPermR of sigma is conjugate, through the reduction
equivalence, to the q-Frobenius permutation permBar. -/
theorem S2673_reductionEquiv_rootPerm (f : R10[X]) (p : Ideal R10) [hp : p.IsMaximal]
    (P : Ideal T10) [hP : P.IsPrime] [hPover : P.LiesOver p] [hPmax : P.IsMaximal]
    (hmonic : f.Monic) (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
    (hsplit : (f.map (algebraMap R10 L10)).Splits) (hdeg : f.natDegree ≠ 0)
    (hsepK : (f.map (algebraMap R10 K)).Separable)
    [Fintype (R10 ⧸ p)] [Fintype (T10 ⧸ P)]
    (sigma : Gal(L10/K)) (H : IsArithFrobAt R10 sigma P) :
    (S2673_reductionEquiv f p P hmonic hsep hsplit hdeg hsepK).permCongr
        (S2532LocalizedDefinitionsActual.rootPermR R10 K L10 f hsplit sigma) =
      permBar (f := f) (p := p) (P := P) := by
  apply Equiv.ext
  intro z
  rw [Equiv.permCongr_apply]
  obtain ⟨y, rfl⟩ := (S2673_reductionEquiv f p P hmonic hsep hsplit hdeg hsepK).surjective z
  rw [Equiv.symm_apply_apply]
  have hroot : S2532LocalizedDefinitionsActual.rootPermR R10 K L10 f hsplit sigma y = sigma • y := by
    apply Subtype.ext
    simp only [S2532LocalizedDefinitionsActual.rootPermR, MulAction.toPermHom_apply,
      MulAction.toPerm_apply, Polynomial.rootSet.coe_smul, AlgEquiv.smul_def]
  rw [hroot, S2673_reductionEquiv_apply, S2673_rootSetKEquiv_smul, S2673_toS_smul,
    S2673_redRoot_smul (f := f) (p := p) (P := P) (hmonic := hmonic) (hsep := hsep)
      (hsplit := hsplit) (sigma := sigma) (H := H)]
  rw [S2673_reductionEquiv_apply]

/-! ## 5. Conjugacy invariance of the orbit-size multiset -/

lemma S2673_orbitSizeMultiset_permCongr {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (e : alpha ≃ beta) (tau : Equiv.Perm alpha) :
    S2217DedekindFrobTheoremActual.orbitSizeMultiset (e.permCongr tau) =
      S2217DedekindFrobTheoremActual.orbitSizeMultiset tau := by
  classical
  have hcyc : (e.permCongr tau).cycleType = tau.cycleType :=
    LeanFormal.IUT.XiFPaper.S2132FrobCycleActual.S2132cycleType_permCongr e tau
  have hfix : Fintype.card (Function.fixedPoints (e.permCongr tau)) =
      Fintype.card (Function.fixedPoints tau) := by
    rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.card_fixedPoints, hcyc,
      Fintype.card_congr e]
  simp only [S2217DedekindFrobTheoremActual.orbitSizeMultiset, hcyc, hfix,
    Fintype.card_congr e]

/-! ## 6. The orbit-size multiset of permBar is factorDegrees -/

lemma S2673_filter_ne_one_add_replicate_count_one (M : Multiset Nat) :
    M.filter (fun n => n ≠ 1) + Multiset.replicate (M.count 1) 1 = M := by
  classical
  ext n
  rw [Multiset.count_add, Multiset.count_filter, Multiset.count_replicate]
  by_cases hn : n = 1
  · subst hn; simp
  · have h1n : ¬ (1 = n) := fun h => hn h.symm
    simp [hn, h1n]

lemma S2673_factorDegrees_sum (f : R10[X]) (p : Ideal R10) [hp : p.IsMaximal]
    (hmonic : f.Monic) :
    (factorDegrees (fbar f p)).sum = f.natDegree := by
  classical
  have hmonicbar : (fbar f p).Monic := hmonic.map _
  have hne : fbar f p ≠ 0 := hmonicbar.ne_zero
  have hprod : (UniqueFactorizationMonoid.normalizedFactors (fbar f p)).prod = fbar f p := by
    have h := Polynomial.leadingCoeff_mul_prod_normalizedFactors (fbar f p)
    rw [hmonicbar.leadingCoeff, map_one, one_mul] at h
    exact h
  unfold LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual.factorDegrees
  rw [← Polynomial.natDegree_multiset_prod_of_monic]
  · rw [hprod]
    exact Polynomial.Monic.natDegree_map hmonic (Ideal.Quotient.mk p)
  · intro g hg
    exact ((Polynomial.mem_normalizedFactors_iff hne).mp hg).2.1

/-- The orbit-size multiset of the q-Frobenius permutation of the roots of
f mod p is the multiset of factor degrees. -/
theorem S2673_orbitSizeMultiset_permBar (f : R10[X]) (p : Ideal R10) [hp : p.IsMaximal]
    (P : Ideal T10) [hP : P.IsPrime] [hPover : P.LiesOver p] [hPmax : P.IsMaximal]
    [Fintype (R10 ⧸ p)] [Fintype (T10 ⧸ P)]
    [DecidableEq (R10 ⧸ p)] [DecidableEq (T10 ⧸ P)]
    (hmonic : f.Monic) (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
    (hsplit : (f.map (algebraMap R10 L10)).Splits) :
    S2217DedekindFrobTheoremActual.orbitSizeMultiset
        (permBar (f := f) (p := p) (P := P)) =
      factorDegrees (fbar f p) := by
  classical
  have hcyc := S2548ConcreteCycleTypeActual.concrete_permBar_cycleType
    (f := f) (p := p) (P := P) (hmonic := hmonic) (hsep := hsep) (hsplit := hsplit)
  have hinst : (Classical.decEq ((fbar f p).rootSet (T10 ⧸ P))) =
      (fun a b => Subtype.instDecidableEq a b) := by
    funext a b
    exact Subsingleton.elim _ _
  have hcyc' : (@Equiv.Perm.cycleType ((fbar f p).rootSet (T10 ⧸ P)) _
      (Classical.decEq _) (permBar (f := f) (p := p) (P := P))) =
      (factorDegrees (fbar f p)).filter (fun n => n ≠ 1) := by
    rw [hinst]
    exact hcyc
  have hcard : Fintype.card ((fbar f p).rootSet (T10 ⧸ P)) = f.natDegree := by
    rw [← Fintype.card_congr (Equiv.ofBijective _
      (redRoot_bijective (f := f) (p := p) (P := P) (hmonic := hmonic)
        (hsep := hsep) (hsplit := hsplit)))]
    exact card_rootSet_eq (f := f) (p := p) (P := P) (hmonic := hmonic)
      (hsep := hsep) (hsplit := hsplit)
  have hsum : (factorDegrees (fbar f p)).sum = f.natDegree :=
    S2673_factorDegrees_sum f p hmonic
  have hcount : (factorDegrees (fbar f p)).count 1 =
      f.natDegree - ((factorDegrees (fbar f p)).filter (fun n => n ≠ 1)).sum := by
    have hid := S2673_filter_ne_one_add_replicate_count_one (factorDegrees (fbar f p))
    have hsumid : ((factorDegrees (fbar f p)).filter (fun n => n ≠ 1)).sum +
        (factorDegrees (fbar f p)).count 1 = f.natDegree := by
      have h := congrArg Multiset.sum hid
      rw [Multiset.sum_add, Multiset.sum_replicate, hsum] at h
      simpa using h
    omega
  simp only [S2217DedekindFrobTheoremActual.orbitSizeMultiset]
  rw [@Equiv.Perm.card_fixedPoints _ _ (Classical.decEq _), hcyc', hcard, ← hcount]
  exact S2673_filter_ne_one_add_replicate_count_one (factorDegrees (fbar f p))

/-! ## 7. The localized orbit-size theorem -/

/-- The localized Dedekind--Frobenius orbit-size theorem. For a monic
f : R[X], a maximal ideal p of R, a prime P of T10 over p, and an
arithmetic Frobenius sigma at P, the orbit-size multiset of sigma on the roots
of f in L is the multiset of degrees of the irreducible factors of f mod p. -/
theorem S2673_localized_orbitSizeMultiset_eq_factorDegrees
    (f : R10[X]) (p : Ideal R10) [hp : p.IsMaximal]
    (P : Ideal T10) [hP : P.IsPrime] [hPover : P.LiesOver p] [hPmax : P.IsMaximal]
    [Fintype (R10 ⧸ p)] [Fintype (T10 ⧸ P)]
    [DecidableEq (R10 ⧸ p)] [DecidableEq (T10 ⧸ P)]
    (hmonic : f.Monic) (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
    (hsplit : (f.map (algebraMap R10 L10)).Splits) (hdeg : f.natDegree ≠ 0)
    (hsepK : (f.map (algebraMap R10 K)).Separable)
    (sigma : Gal(L10/K)) (H : IsArithFrobAt R10 sigma P) :
    S2217DedekindFrobTheoremActual.orbitSizeMultiset
        (S2532LocalizedDefinitionsActual.rootPermR R10 K L10 f hsplit sigma) =
      factorDegrees (fbar f p) := by
  classical
  rw [← S2673_orbitSizeMultiset_permCongr
    (S2673_reductionEquiv f p P hmonic hsep hsplit hdeg hsepK)
    (S2532LocalizedDefinitionsActual.rootPermR R10 K L10 f hsplit sigma),
    S2673_reductionEquiv_rootPerm (f := f) (p := p) (P := P) (hmonic := hmonic)
      (hsep := hsep) (hsplit := hsplit) (hdeg := hdeg) (hsepK := hsepK) (sigma := sigma) (H := H)]
  exact S2673_orbitSizeMultiset_permBar (f := f) (p := p) (P := P) (hmonic := hmonic)
    (hsep := hsep) (hsplit := hsplit)

end LeanFormal.IUT.XiFPaper.S2673LocalizedOrbitSizeActual
end
