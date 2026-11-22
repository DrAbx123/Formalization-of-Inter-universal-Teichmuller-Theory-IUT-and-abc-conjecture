/-
S2675: the arithmetic Frobenius at p1249R and the localized orbit-size
theorem for the concrete psi_5 model f10' at 1249.

For any prime P of T10 = O_L[1/10] over p1249R (the localised degree-one prime
at 1249), there is an arithmetic Frobenius sigma at P whose orbit-size multiset
on the roots of f10' in L is {2, 10}, the factor degrees of f10' modulo p1249R.

No sorry, axiom, True/PUnit or native_decide is used.
-/
import tmp.sheaf.xif.paper.S2674LocalizedOrbitSize1249Actual
import tmp.sheaf.xif.paper.S2598bHsepSplitActual

noncomputable section
set_option maxHeartbeats 32000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2674LocalizedOrbitSize1249Actual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2671Mod1249FactorDegreesActual
open LeanFormal.IUT.XiFPaper.S2577Away10FbarActual

namespace LeanFormal.IUT.XiFPaper.S2675LocalizedOrbit1249Actual

abbrev A : Type := S2537ConcreteLocalizationActual.A
abbrev R10 : Type := S2537ConcreteLocalizationActual.R
abbrev T10 : Type := S2537ConcreteLocalizationActual.S
abbrev OL : Type := S2537ConcreteLocalizationActual.C
abbrev K : Type := S2537ConcreteLocalizationActual.K
abbrev L10 : Type := S2537ConcreteLocalizationActual.L

attribute [local instance] Ideal.Quotient.field

local instance : Fact (Nat.Prime 1249) := ⟨by norm_num⟩

/-! ## 1. The prime 1249 in p1249R -/

theorem S2675_int1249_eq_R10 (z : ℤ) :
    algebraMap R10 T10 (algebraMap ℤ R10 z) = algebraMap ℤ T10 z := by
  have h1 : algebraMap ℤ R10 z = (z : R10) := by simp
  have h2 : algebraMap ℤ T10 z = (z : T10) := by simp
  rw [h1, h2]
  simp

theorem S2675_int1249_mem_T10 (P : Ideal T10) [hPover : P.LiesOver p1249R] :
    algebraMap ℤ T10 (1249 : ℤ) ∈ P := by
  have h : algebraMap ℤ R10 (1249 : ℤ) ∈ P.under R10 := by
    rw [show P.under R10 = p1249R from hPover.over.symm]
    exact S2674_int1249_mem_p1249R
  rw [Ideal.under_def, Ideal.mem_comap, S2675_int1249_eq_R10] at h
  exact h

theorem S2675_int1249_eq_OL (z : ℤ) :
    algebraMap OL T10 (algebraMap ℤ OL z) = algebraMap ℤ T10 z := by
  have h1 : algebraMap ℤ OL z = (z : OL) := by simp
  have h2 : algebraMap ℤ T10 z = (z : T10) := by simp
  rw [h1, h2]
  simp

theorem S2675_under_OL_ne_bot (P : Ideal T10) [hP : P.IsPrime] [hPover : P.LiesOver p1249R] :
    P.under OL ≠ ⊥ := by
  intro hbot
  have h1249T : algebraMap ℤ T10 (1249 : ℤ) ∈ P := S2675_int1249_mem_T10 P
  have hmem : algebraMap ℤ OL (1249 : ℤ) ∈ P.under OL := by
    rw [Ideal.under_def, Ideal.mem_comap, S2675_int1249_eq_OL]
    exact h1249T
  rw [hbot] at hmem
  have hne' : (1249 : L10) ≠ 0 := by norm_num
  have hne : algebraMap ℤ OL (1249 : ℤ) ≠ 0 := by
    intro h0
    apply hne'
    have h1 := congrArg (algebraMap OL L10) h0
    rw [map_zero] at h1
    have h2 : (algebraMap OL L10) ((algebraMap ℤ OL) (1249 : ℤ)) = (1249 : L10) := by
      rw [show algebraMap ℤ OL (1249 : ℤ) = (1249 : OL) by norm_num]
      simpa using map_natCast (algebraMap OL L10) 1249
    rwa [h2] at h1
  exact hne (Ideal.mem_bot.mp hmem)

theorem S2675_under_OL_max (P : Ideal T10) [hP : P.IsPrime] [hPover : P.LiesOver p1249R] :
    (P.under OL).IsMaximal := by
  haveI hfin : Finite (OL ⧸ P.under OL) :=
    Ring.HasFiniteQuotients.finiteQuotient (S2675_under_OL_ne_bot P)
  haveI : IsDomain (OL ⧸ P.under OL) := Ideal.Quotient.isDomain (P.under OL)
  exact Ideal.Quotient.maximal_of_isField (P.under OL)
    (Finite.isField_of_domain (OL ⧸ P.under OL))

noncomputable def S2675_residueEquiv (P : Ideal T10) [hP : P.IsPrime]
    [hPover : P.LiesOver p1249R] :
    (OL ⧸ P.under OL) ≃+* (T10 ⧸ P) :=
  letI := S2675_under_OL_max P
  LeanFormal.IUT.XiFPaper.S2592GenericLocalizedResidueIsoActual.localizedResidueEquiv
    (R := OL) (T := T10)
    (M := Algebra.algebraMapSubmonoid OL (Submonoid.powers (10 : A)))
    (I := P.under OL) (P := P) rfl

noncomputable instance S2675_fintype_quot (P : Ideal T10) [hP : P.IsPrime]
    [hPover : P.LiesOver p1249R] : Fintype (T10 ⧸ P) := by
  haveI hfin : Finite (OL ⧸ P.under OL) :=
    Ring.HasFiniteQuotients.finiteQuotient (S2675_under_OL_ne_bot P)
  haveI : Fintype (OL ⧸ P.under OL) := Fintype.ofFinite _
  exact Fintype.ofEquiv (OL ⧸ P.under OL) (S2675_residueEquiv P)

instance S2675_decEq_quot (P : Ideal T10) [hP : P.IsPrime]
    [hPover : P.LiesOver p1249R] : DecidableEq (T10 ⧸ P) := Classical.decEq _

/-! ## 2. Separability and the orbit-size theorem at 1249 -/

theorem S2675_separable_psiZ :
    (Polynomial.C (415 : ZMod 1249) * (S2550F2 * S2550F10)).Separable := by
  classical
  rw [PerfectField.separable_iff_squarefree]
  have hc_ne : (415 : ZMod 1249) ≠ 0 := by decide
  have hcC : (Polynomial.C (415 : ZMod 1249) : (ZMod 1249)[X]) ≠ 0 :=
    Polynomial.C_ne_zero.mpr hc_ne
  have hg2 : S2550F2 ≠ 0 := S2671F2_monic.ne_zero
  have hg10 : S2550F10 ≠ 0 := S2671F10_monic.ne_zero
  have hprod : S2550F2 * S2550F10 ≠ 0 := mul_ne_zero hg2 hg10
  have hmain : Polynomial.C (415 : ZMod 1249) * (S2550F2 * S2550F10) ≠ 0 :=
    mul_ne_zero hcC hprod
  rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hmain]
  have hnf : UniqueFactorizationMonoid.normalizedFactors
      (Polynomial.C (415 : ZMod 1249) * (S2550F2 * S2550F10)) =
      (S2550F2 ::ₘ S2550F10 ::ₘ 0 : Multiset (ZMod 1249)[X]) := by
    rw [UniqueFactorizationMonoid.normalizedFactors_mul hcC hprod,
      UniqueFactorizationMonoid.normalizedFactors_of_isUnit
        (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc_ne)),
      Multiset.zero_add,
      UniqueFactorizationMonoid.normalizedFactors_mul hg2 hg10,
      UniqueFactorizationMonoid.normalizedFactors_irreducible S2671F2_irreducible,
      UniqueFactorizationMonoid.normalizedFactors_irreducible S2671F10_irreducible,
      Monic.normalize_eq_self S2671F2_monic, Monic.normalize_eq_self S2671F10_monic]
    simp
  rw [hnf]
  have hne : S2550F2 ≠ S2550F10 := by
    intro h
    have h2 : (2 : ℕ) = 10 := by
      rw [← S2671F2_degree, ← S2671F10_degree, h]
    norm_num at h2
  simp [Multiset.nodup_cons, hne]

theorem S2675_hsep : (fbar f10' p1249R).Separable := by
  refine (Polynomial.separable_map residueEquivR1249.toRingHom).mp ?_
  rw [S2674_fbar_map_eq, ← S2550Psi5Mod1249_eq, S2550Product]
  exact Polynomial.Separable.unit_mul
    (isUnit_C.mpr (u_isUnit.map (residueEquivR1249.toRingHom.comp
      (Ideal.Quotient.mk p1249R)).toMonoidHom))
    S2675_separable_psiZ

theorem S2675_f10'_natDegree_ne_zero : f10'.natDegree ≠ 0 := by
  rw [f10'_natDegree]
  norm_num

theorem S2675_f10'_hsepK : (f10'.map (algebraMap R10 K)).Separable := by
  rw [show f10'.map (algebraMap R10 K) =
      Polynomial.C ((5 : K)⁻¹) * S2057Psi5F from f10'_map_scalar]
  exact Polynomial.Separable.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by norm_num)))
    S2057Psi5F_separable

/-- The localized orbit-size theorem at 1249: for every prime P of T10 over
p1249R there is an arithmetic Frobenius at P whose orbit-size multiset on the
roots of f10' is {2, 10}. -/
theorem S2675_localized_orbitSize_1249 (P : Ideal T10) [hP : P.IsPrime]
    [hPover : P.LiesOver p1249R] :
    ∃ sigma : Gal(L10/K), IsArithFrobAt R10 sigma P ∧
      S2217DedekindFrobTheoremActual.orbitSizeMultiset
        (S2532LocalizedDefinitionsActual.rootPermR R10 K L10 f10'
          S2598bHsepSplitActual.S2598b_hsplit sigma) = ({2, 10} : Multiset ℕ) := by
  classical
  haveI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (p := p1249R) (P := P)
  haveI : Fintype (T10 ⧸ P) := S2675_fintype_quot P
  haveI hInv : Algebra.IsInvariant R10 T10 Gal(L10/K) :=
    Algebra.isInvariant_of_isGalois R10 K L10 T10
  obtain ⟨sigma, H⟩ := IsArithFrobAt.exists_of_isInvariant (S := T10) R10 (Gal(L10/K)) P
  refine ⟨sigma, H, ?_⟩
  rw [S2673LocalizedOrbitSizeActual.S2673_localized_orbitSizeMultiset_eq_factorDegrees
    (f := f10') (p := p1249R) (P := P)
    S2598bHsepSplitActual.S2598b_hmonic S2675_hsep
    S2598bHsepSplitActual.S2598b_hsplit S2675_f10'_natDegree_ne_zero
    S2675_f10'_hsepK sigma H,
    S2674LocalizedOrbitSize1249Actual.S2674_factorDegrees_fbar]

/-- Existence form: there is a prime of T10 over p1249R and an arithmetic
Frobenius at it with orbit-size multiset {2, 10}. -/
theorem S2675_exists_localized_orbitSize_1249 :
    ∃ (P : Ideal T10) (sigma : Gal(L10/K)),
      P.IsPrime ∧ P.LiesOver p1249R ∧ IsArithFrobAt R10 sigma P ∧
      S2217DedekindFrobTheoremActual.orbitSizeMultiset
        (S2532LocalizedDefinitionsActual.rootPermR R10 K L10 f10'
          S2598bHsepSplitActual.S2598b_hsplit sigma) = ({2, 10} : Multiset ℕ) := by
  obtain ⟨P, hPmax, hPover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := R10) (S := T10) p1249R
  haveI : P.IsMaximal := hPmax
  haveI : P.IsPrime := hPmax.isPrime
  haveI : P.LiesOver p1249R := hPover
  obtain ⟨sigma, H, hcyc⟩ := S2675_localized_orbitSize_1249 P
  exact ⟨P, sigma, hPmax.isPrime, hPover, H, hcyc⟩

end LeanFormal.IUT.XiFPaper.S2675LocalizedOrbit1249Actual
end
