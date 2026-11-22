/-
S2674: the concrete prime p1249R of R = O_{F'}[1/10] and the factor degrees of
f10' modulo p1249R.

The prime is obtained from a degree-one prime p of O_{F'} over 1249
(S2669, unconditional) and localised at 10.  Its residue field is ZMod 1249,
and the reduction of the localised psi_5 model f10' modulo p1249R has factor
degrees {2, 10} (via the explicit ZMod 1249 factorisation of S2550 and S2671).

No sorry, axiom, True/PUnit or native_decide is used.
-/
import tmp.sheaf.xif.paper.S2673LocalizedOrbitSizeActual
import tmp.sheaf.xif.paper.S2577Away10FbarActual
import tmp.sheaf.xif.paper.S2671Mod1249FactorDegreesActual
import tmp.sheaf.xif.paper.S2669Kummer1249Actual
import tmp.sheaf.xif.paper.S2592GenericLocalizedResidueIsoActual

noncomputable section
set_option maxHeartbeats 32000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2577Away10FbarActual
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2671Mod1249FactorDegreesActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2592GenericLocalizedResidueIsoActual
open LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual

namespace LeanFormal.IUT.XiFPaper.S2674LocalizedOrbitSize1249Actual

attribute [local instance] Ideal.Quotient.field

abbrev A : Type := S2537ConcreteLocalizationActual.A
abbrev R10 : Type := S2537ConcreteLocalizationActual.R
abbrev T10 : Type := S2537ConcreteLocalizationActual.S
abbrev OL : Type := S2537ConcreteLocalizationActual.C
abbrev K : Type := S2537ConcreteLocalizationActual.K
abbrev L10 : Type := S2537ConcreteLocalizationActual.L
abbrev M : Submonoid A := Submonoid.powers (10 : A)

local instance : Fact (Nat.Prime 1249) := ⟨by norm_num⟩

/-! ## 1. The degree-one prime of O_{F'} at 1249 -/

theorem S2674_exists_prime1249 :
    ∃ (p : Ideal A) (e : A ⧸ p ≃+* ZMod 1249),
      p.IsPrime ∧ p.LiesOver (Ideal.span ({(1249 : ℤ)} : Set ℤ)) := by
  obtain ⟨p, hp, hpl, -, ⟨e⟩, -⟩ :=
    LeanFormal.IUT.XiFPaper.S2669Kummer1249Actual.S2669_exists_primeDegreeOne
  exact ⟨p, e, hp, hpl⟩

noncomputable def p1249A : Ideal A := Classical.choose S2674_exists_prime1249

noncomputable def e1249A : A ⧸ p1249A ≃+* ZMod 1249 :=
  Classical.choose (Classical.choose_spec S2674_exists_prime1249)

theorem p1249A_spec : p1249A.IsPrime ∧
    p1249A.LiesOver (Ideal.span ({(1249 : ℤ)} : Set ℤ)) :=
  Classical.choose_spec (Classical.choose_spec S2674_exists_prime1249)

theorem p1249A_prime : p1249A.IsPrime := p1249A_spec.1

theorem p1249A_lies : p1249A.LiesOver (Ideal.span ({(1249 : ℤ)} : Set ℤ)) :=
  p1249A_spec.2

theorem S2674_int1249_mem_p1249A : algebraMap ℤ A (1249 : ℤ) ∈ p1249A := by
  have h : (1249 : ℤ) ∈ p1249A.under ℤ := by
    rw [p1249A_lies.over.symm]
    exact Ideal.mem_span_singleton_self 1249
  rw [Ideal.under_def, Ideal.mem_comap] at h
  exact h

theorem S2674_int1249_ne_zero : algebraMap ℤ A (1249 : ℤ) ≠ 0 := by
  intro h
  have h1 : algebraMap A K (algebraMap ℤ A (1249 : ℤ)) = 0 := by rw [h, map_zero]
  rw [← IsScalarTower.algebraMap_apply ℤ A K] at h1
  norm_num at h1

instance S2674_p1249A_isMaximal : p1249A.IsMaximal := by
  haveI : IsDedekindDomain A := inferInstance
  refine Ideal.IsPrime.isMaximal p1249A_prime ?_
  intro hbot
  have hmem := S2674_int1249_mem_p1249A
  rw [hbot] at hmem
  exact S2674_int1249_ne_zero (Ideal.mem_bot.mp hmem)

theorem S2674_ten_not_mem_p1249A : algebraMap ℤ A (10 : ℤ) ∉ p1249A := by
  intro hx
  have h : (10 : ℤ) ∈ p1249A.under ℤ := by
    rw [Ideal.under_def, Ideal.mem_comap]
    exact hx
  rw [p1249A_lies.over.symm] at h
  have hdvd := Ideal.mem_span_singleton.mp h
  norm_num at hdvd

theorem S2674_disjoint : Disjoint (M : Set A) (p1249A : Set A) := by
  rw [Set.disjoint_left]
  intro x hx hxp
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff x (10 : A)).mp hx
  have h10 : (10 : A) ∈ p1249A := by
    have hpow : (10 : A) ^ n ∈ p1249A := by
      rw [hn]
      exact hxp
    exact p1249A_prime.mem_of_pow_mem n hpow
  apply S2674_ten_not_mem_p1249A
  rwa [show algebraMap ℤ A (10 : ℤ) = (10 : A) from by norm_num]

/-! ## 2. The localised prime p1249R and its residue field -/

/-- The prime of R = O_{F'}[1/10] induced by the degree-one prime at 1249. -/
def p1249R : Ideal R10 := p1249A.map (algebraMap A R10)

theorem S2674_p1249R_prime : p1249R.IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint M R10 p1249A p1249A_prime S2674_disjoint

theorem S2674_p1249R_lies : p1249R.LiesOver p1249A :=
  IsLocalization.liesOver_map_of_isPrime_disjoint M R10 S2674_disjoint

theorem S2674_int1249_mem_p1249R : algebraMap ℤ R10 (1249 : ℤ) ∈ p1249R := by
  rw [IsScalarTower.algebraMap_apply ℤ A R10]
  exact Ideal.mem_map_of_mem (algebraMap A R10) S2674_int1249_mem_p1249A

theorem S2674_int1249_ne_zero_R10 : algebraMap ℤ R10 (1249 : ℤ) ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply ℤ A R10]
  have hM : Submonoid.powers (10 : A) ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (by norm_num : (10 : A) ≠ 0)
  have hinj : Function.Injective (algebraMap A R10) :=
    IsLocalization.injective (S := R10) hM
  exact fun h => S2674_int1249_ne_zero
    (hinj (show algebraMap A R10 (algebraMap ℤ A (1249 : ℤ)) = algebraMap A R10 0 from by
      rw [h, map_zero]))

instance S2674_p1249R_isMaximal : p1249R.IsMaximal := by
  haveI : IsDedekindDomain R10 := inferInstance
  refine Ideal.IsPrime.isMaximal S2674_p1249R_prime ?_
  intro hbot
  have hmem := S2674_int1249_mem_p1249R
  rw [hbot] at hmem
  exact S2674_int1249_ne_zero_R10 (Ideal.mem_bot.mp hmem)

noncomputable instance S2674_field_quot_p1249R : Field (R10 ⧸ p1249R) :=
  Ideal.Quotient.field p1249R

theorem S2674_p1249R_under :
    p1249R.comap (algebraMap A R10) = p1249A :=
  IsLocalization.under_map_of_isPrime_disjoint M R10 p1249A_prime S2674_disjoint

/-- The residue isomorphism R/p1249R =+* ZMod 1249. -/
noncomputable def residueEquivR1249 : R10 ⧸ p1249R ≃+* ZMod 1249 :=
  (localizedResidueEquiv (M := M) (I := p1249A) (P := p1249R)
    S2674_p1249R_under).symm.trans e1249A

noncomputable instance p1249R_fintype : Fintype (R10 ⧸ p1249R) :=
  Fintype.ofEquiv (ZMod 1249) residueEquivR1249.symm

instance p1249R_decEq : DecidableEq (R10 ⧸ p1249R) := Classical.decEq _

theorem S2674_comp_int :
    (residueEquivR1249.toRingHom.comp (Ideal.Quotient.mk p1249R)).comp
      (algebraMap ℤ R10) = Int.castRingHom (ZMod 1249) :=
  RingHom.ext_int _ _

lemma S2674_quotsymm_comp_symm :
    residueEquivR1249.toRingHom.comp residueEquivR1249.symm.toRingHom =
      RingHom.id (ZMod 1249) := by
  ext x
  exact RingEquiv.apply_symm_apply residueEquivR1249 x

lemma S2674_coe_comp_symm :
    ((residueEquivR1249 : R10 ⧸ p1249R →+* ZMod 1249).comp
        residueEquivR1249.symm.toRingHom) = RingHom.id (ZMod 1249) :=
  S2674_quotsymm_comp_symm

/-! ## 3. The factorisation of f10' modulo p1249R -/

/-- The reduction of f10' modulo p1249R, transported to ZMod 1249. -/
theorem S2674_fbar_map_eq :
    (fbar f10' p1249R).map residueEquivR1249.toRingHom =
      Polynomial.C ((residueEquivR1249.toRingHom.comp (Ideal.Quotient.mk p1249R)) u) *
        S2132Psi5Z.map (Int.castRingHom (ZMod 1249)) := by
  show (f10'.map (Ideal.Quotient.mk p1249R)).map residueEquivR1249.toRingHom = _
  rw [Polynomial.map_map]
  unfold LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.f10'
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, S2674_comp_int]

lemma S2674_mapEquiv_F2 :
    (Polynomial.mapEquiv residueEquivR1249)
        (S2550F2.map residueEquivR1249.symm.toRingHom) = S2550F2 := by
  simp only [Polynomial.mapEquiv_apply, Polynomial.map_map, S2674_quotsymm_comp_symm,
    S2674_coe_comp_symm, Polynomial.map_id]

lemma S2674_mapEquiv_F10 :
    (Polynomial.mapEquiv residueEquivR1249)
        (S2550F10.map residueEquivR1249.symm.toRingHom) = S2550F10 := by
  simp only [Polynomial.mapEquiv_apply, Polynomial.map_map, S2674_quotsymm_comp_symm,
    S2674_coe_comp_symm, Polynomial.map_id]

lemma S2674_F2_map_monic :
    (S2550F2.map residueEquivR1249.symm.toRingHom).Monic :=
  S2671F2_monic.map _

lemma S2674_F10_map_monic :
    (S2550F10.map residueEquivR1249.symm.toRingHom).Monic :=
  S2671F10_monic.map _

lemma S2674_F2_map_irreducible :
    Irreducible (S2550F2.map residueEquivR1249.symm.toRingHom) := by
  have h1 : Irreducible ((Polynomial.mapEquiv residueEquivR1249)
      (S2550F2.map residueEquivR1249.symm.toRingHom)) := by
    rw [S2674_mapEquiv_F2]
    exact S2671F2_irreducible
  exact (MulEquiv.irreducible_iff (f := Polynomial.mapEquiv residueEquivR1249)).mp h1

lemma S2674_F10_map_irreducible :
    Irreducible (S2550F10.map residueEquivR1249.symm.toRingHom) := by
  have h1 : Irreducible ((Polynomial.mapEquiv residueEquivR1249)
      (S2550F10.map residueEquivR1249.symm.toRingHom)) := by
    rw [S2674_mapEquiv_F10]
    exact S2671F10_irreducible
  exact (MulEquiv.irreducible_iff (f := Polynomial.mapEquiv residueEquivR1249)).mp h1

lemma S2674_F2_map_degree :
    (S2550F2.map residueEquivR1249.symm.toRingHom).natDegree = 2 := by
  rw [Polynomial.natDegree_map_eq_of_injective residueEquivR1249.symm.injective]
  exact S2671F2_degree

lemma S2674_F10_map_degree :
    (S2550F10.map residueEquivR1249.symm.toRingHom).natDegree = 10 := by
  rw [Polynomial.natDegree_map_eq_of_injective residueEquivR1249.symm.injective]
  exact S2671F10_degree

theorem S2674_c_ne_zero :
    (Ideal.Quotient.mk p1249R) u * residueEquivR1249.symm (415 : ZMod 1249) ≠ 0 := by
  have h1 : IsUnit ((Ideal.Quotient.mk p1249R) u) :=
    u_isUnit.map (Ideal.Quotient.mk p1249R).toMonoidHom
  have h2 : residueEquivR1249.symm (415 : ZMod 1249) ≠ 0 := by
    intro h
    have hc := congrArg residueEquivR1249 h
    rw [RingEquiv.apply_symm_apply, map_zero] at hc
    exact (by decide : (415 : ZMod 1249) ≠ 0) hc
  exact mul_ne_zero h1.ne_zero h2

/-- The factorisation of f10' modulo p1249R, over R/p1249R. -/
theorem S2674_fbar_factorization :
    fbar f10' p1249R =
      Polynomial.C ((Ideal.Quotient.mk p1249R) u * residueEquivR1249.symm 415) *
        ((S2550F2.map residueEquivR1249.symm.toRingHom) *
          (S2550F10.map residueEquivR1249.symm.toRingHom)) := by
  have hc_eq : residueEquivR1249
        ((Ideal.Quotient.mk p1249R) u * residueEquivR1249.symm 415) =
      ((residueEquivR1249.toRingHom.comp (Ideal.Quotient.mk p1249R)) u) * 415 := by
    rw [map_mul, RingEquiv.apply_symm_apply]
    rfl
  have hc_eq' : residueEquivR1249.toRingHom
        ((Ideal.Quotient.mk p1249R) u * residueEquivR1249.symm 415) =
      ((residueEquivR1249.toRingHom.comp (Ideal.Quotient.mk p1249R)) u) * 415 :=
    hc_eq
  have hR : (Polynomial.C ((Ideal.Quotient.mk p1249R) u * residueEquivR1249.symm 415) *
        ((S2550F2.map residueEquivR1249.symm.toRingHom) *
          (S2550F10.map residueEquivR1249.symm.toRingHom))).map
        residueEquivR1249.toRingHom =
      Polynomial.C (((residueEquivR1249.toRingHom.comp (Ideal.Quotient.mk p1249R)) u) * 415) *
        (S2550F2 * S2550F10) := by
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map,
      S2674_quotsymm_comp_symm, S2674_coe_comp_symm, Polynomial.map_id, hc_eq']
  have hL : (fbar f10' p1249R).map residueEquivR1249.toRingHom =
      Polynomial.C (((residueEquivR1249.toRingHom.comp (Ideal.Quotient.mk p1249R)) u) * 415) *
        (S2550F2 * S2550F10) := by
    rw [S2674_fbar_map_eq, ← S2550Psi5Mod1249_eq, S2550Product]
    exact (mul_assoc _ _ _).symm.trans (by rw [Polynomial.C_mul])
  exact Polynomial.map_injective residueEquivR1249.toRingHom
    residueEquivR1249.injective (by rw [hL, hR])

/-- The reduction of the localised psi_5 model modulo 1249 has factor
degrees {2, 10}. -/
theorem S2674_factorDegrees_fbar :
    factorDegrees (fbar f10' p1249R) = ({2, 10} : Multiset ℕ) := by
  rw [S2674_fbar_factorization]
  exact S2671_factorDegrees_of_factors _ S2674_c_ne_zero _ _
    S2674_F2_map_monic S2674_F10_map_monic S2674_F2_map_irreducible
    S2674_F10_map_irreducible S2674_F2_map_degree S2674_F10_map_degree

theorem S2674_fbar_separable : (fbar f10' p1249R).Separable := by
  classical
  letI : Field (R10 ⧸ p1249R) := Ideal.Quotient.field p1249R
  rw [S2674_fbar_factorization]
  set F2' : (R10 ⧸ p1249R)[X] := S2550F2.map residueEquivR1249.symm.toRingHom
  set F10' : (R10 ⧸ p1249R)[X] := S2550F10.map residueEquivR1249.symm.toRingHom
  have h2irr : Irreducible F2' := S2674_F2_map_irreducible
  have h10irr : Irreducible F10' := S2674_F10_map_irreducible
  have h2monic : F2'.Monic := S2674_F2_map_monic
  have h10monic : F10'.Monic := S2674_F10_map_monic
  have h2deg : F2'.natDegree = 2 := S2674_F2_map_degree
  have h10deg : F10'.natDegree = 10 := S2674_F10_map_degree
  have h2sep : F2'.Separable := PerfectField.separable_of_irreducible h2irr
  have h10sep : F10'.Separable := PerfectField.separable_of_irreducible h10irr
  have hcop : IsCoprime F2' F10' := by
    rcases h2irr.isCoprime_or_dvd F10' with h | hdvd
    · exact h
    · exfalso
      have hassoc : Associated F2' F10' := h2irr.associated_of_dvd h10irr hdvd
      have heq : F2' = F10' := Polynomial.eq_of_monic_of_associated h2monic h10monic hassoc
      rw [heq, h10deg] at h2deg
      norm_num at h2deg
  have hprod : (F2' * F10').Separable := h2sep.mul h10sep hcop
  have hcunit : IsUnit (Polynomial.C
      ((Ideal.Quotient.mk p1249R) u * residueEquivR1249.symm (415 : ZMod 1249))) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr S2674_c_ne_zero)
  have h' : ((F2' * F10') * Polynomial.C
      ((Ideal.Quotient.mk p1249R) u * residueEquivR1249.symm (415 : ZMod 1249))).Separable :=
    hprod.mul_unit hcunit
  simpa [mul_comm, mul_left_comm, mul_assoc] using h'

#check S2674_fbar_separable

end LeanFormal.IUT.XiFPaper.S2674LocalizedOrbitSize1249Actual
end
