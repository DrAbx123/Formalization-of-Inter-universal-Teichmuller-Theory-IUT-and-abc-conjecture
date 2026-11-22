/-
S2673: factor degrees of the localised D5 model f10 modulo a prime over 1249.

Let R = O_{F'}[1/10] (S2537ConcreteLocalizationActual.R) and let f10 be the
monic localised psi_5 model of S2660R10ModelActual.  For any prime PR of R with
R / PR =+* ZMod 1249, the reduction f10 mod PR has irreducible factor degrees
{2, 10}.

Proof.  The explicit ZMod 1249 factorisation
  S2550Psi5Mod1249 = C 415 * (F2 * F10)
of S2550 (with F2, F10 irreducible of degrees 2, 10, S2671) is transported
along the residue isomorphism e : R / PR =+* ZMod 1249: the matched factors
F2.map e.symm and F10.map e.symm are monic and irreducible of degrees 2 and 10
over R / PR, and the scalar 415 is absorbed into the leading unit.  Then
S2671_factorDegrees_of_factors computes factorDegrees.

No sorry, axiom, True/PUnit or native_decide is used.
-/
import tmp.sheaf.xif.paper.S2672Away10Prime1249Actual
import tmp.sheaf.xif.paper.S2660R10ModelActual
import tmp.sheaf.xif.paper.S2671Mod1249FactorDegreesActual

noncomputable section
set_option maxHeartbeats 32000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 800000

open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2673F10FactorDegreesActual

open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2660R10ModelActual
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2671Mod1249FactorDegreesActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual

local instance : Fact (Nat.Prime 1249) := ⟨by norm_num⟩

attribute [local instance] Ideal.Quotient.field

/-! ## 0. The defining equation of f10 -/

lemma S2673_f10_def :
    f10 = C ((((S2660u)⁻¹ : Rˣ) : R)) * S2132Psi5Z.map (algebraMap ℤ R) := rfl

/-! ## 1. Compatibility of the residue isomorphism with the prime -/

lemma S2673_comp_int (PR : Ideal R) (e : R ⧸ PR ≃+* ZMod 1249) :
    (e.toRingHom.comp (Ideal.Quotient.mk PR)).comp (algebraMap ℤ R) =
      Int.castRingHom (ZMod 1249) :=
  RingHom.ext_int _ _

lemma S2673_e_comp_symm (PR : Ideal R) (e : R ⧸ PR ≃+* ZMod 1249) :
    e.toRingHom.comp e.symm.toRingHom = RingHom.id (ZMod 1249) := by
  ext x
  exact RingEquiv.apply_symm_apply e x

/-! ## 2. Pulling the explicit factors back along the residue isomorphism -/

lemma S2673_mapEquiv_F2 (PR : Ideal R) [PR.IsMaximal]
    (e : R ⧸ PR ≃+* ZMod 1249) :
    (Polynomial.mapEquiv e) (S2550F2.map e.symm.toRingHom) = S2550F2 := by
  have h : (Polynomial.mapEquiv e).symm S2550F2 =
      S2550F2.map e.symm.toRingHom := rfl
  rw [← h]
  exact (Polynomial.mapEquiv e).apply_symm_apply S2550F2

lemma S2673_mapEquiv_F10 (PR : Ideal R) [PR.IsMaximal]
    (e : R ⧸ PR ≃+* ZMod 1249) :
    (Polynomial.mapEquiv e) (S2550F10.map e.symm.toRingHom) = S2550F10 := by
  have h : (Polynomial.mapEquiv e).symm S2550F10 =
      S2550F10.map e.symm.toRingHom := rfl
  rw [← h]
  exact (Polynomial.mapEquiv e).apply_symm_apply S2550F10

lemma S2673_F2_map_map (PR : Ideal R) [PR.IsMaximal]
    (e : R ⧸ PR ≃+* ZMod 1249) :
    (S2550F2.map e.symm.toRingHom).map e.toRingHom = S2550F2 := by
  have h : (S2550F2.map e.symm.toRingHom).map e.toRingHom =
      (Polynomial.mapEquiv e) (S2550F2.map e.symm.toRingHom) := rfl
  rw [h]
  exact S2673_mapEquiv_F2 PR e

lemma S2673_F10_map_map (PR : Ideal R) [PR.IsMaximal]
    (e : R ⧸ PR ≃+* ZMod 1249) :
    (S2550F10.map e.symm.toRingHom).map e.toRingHom = S2550F10 := by
  have h : (S2550F10.map e.symm.toRingHom).map e.toRingHom =
      (Polynomial.mapEquiv e) (S2550F10.map e.symm.toRingHom) := rfl
  rw [h]
  exact S2673_mapEquiv_F10 PR e

lemma S2673_F2_map_monic (PR : Ideal R) [PR.IsMaximal]
    (e : R ⧸ PR ≃+* ZMod 1249) :
    (S2550F2.map e.symm.toRingHom).Monic :=
  S2671F2_monic.map _

lemma S2673_F10_map_monic (PR : Ideal R) [PR.IsMaximal]
    (e : R ⧸ PR ≃+* ZMod 1249) :
    (S2550F10.map e.symm.toRingHom).Monic :=
  S2671F10_monic.map _

lemma S2673_F2_map_irreducible (PR : Ideal R) [PR.IsMaximal]
    (e : R ⧸ PR ≃+* ZMod 1249) :
    Irreducible (S2550F2.map e.symm.toRingHom) := by
  have h1 : Irreducible ((Polynomial.mapEquiv e)
      (S2550F2.map e.symm.toRingHom)) := by
    rw [S2673_mapEquiv_F2 PR e]
    exact S2671F2_irreducible
  exact (MulEquiv.irreducible_iff (f := Polynomial.mapEquiv e)).mp h1

lemma S2673_F10_map_irreducible (PR : Ideal R) [PR.IsMaximal]
    (e : R ⧸ PR ≃+* ZMod 1249) :
    Irreducible (S2550F10.map e.symm.toRingHom) := by
  have h1 : Irreducible ((Polynomial.mapEquiv e)
      (S2550F10.map e.symm.toRingHom)) := by
    rw [S2673_mapEquiv_F10 PR e]
    exact S2671F10_irreducible
  exact (MulEquiv.irreducible_iff (f := Polynomial.mapEquiv e)).mp h1

lemma S2673_F2_map_degree (PR : Ideal R) [PR.IsMaximal]
    (e : R ⧸ PR ≃+* ZMod 1249) :
    (S2550F2.map e.symm.toRingHom).natDegree = 2 := by
  rw [Polynomial.natDegree_map_eq_of_injective e.symm.injective]
  exact S2671F2_degree

lemma S2673_F10_map_degree (PR : Ideal R) [PR.IsMaximal]
    (e : R ⧸ PR ≃+* ZMod 1249) :
    (S2550F10.map e.symm.toRingHom).natDegree = 10 := by
  rw [Polynomial.natDegree_map_eq_of_injective e.symm.injective]
  exact S2671F10_degree

/-! ## 3. The reduction of psi_5 modulo 1249 -/

lemma S2673_Psi5_mod :
    S2132Psi5Z.map (Int.castRingHom (ZMod 1249)) =
      C (415 : ZMod 1249) * (S2550F2 * S2550F10) := by
  rw [← S2550Psi5Mod1249_eq, S2550Product]

/-! ## 4. The reduction of f10 modulo PR -/

lemma S2673_f10_map_eq (PR : Ideal R) [PR.IsMaximal]
    (e : R ⧸ PR ≃+* ZMod 1249) :
    (f10.map (Ideal.Quotient.mk PR)).map e.toRingHom =
      C ((e.toRingHom.comp (Ideal.Quotient.mk PR))
          ((((S2660u)⁻¹ : Rˣ) : R))) *
        S2132Psi5Z.map (Int.castRingHom (ZMod 1249)) := by
  rw [Polynomial.map_map]
  rw [S2673_f10_def]
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, S2673_comp_int]

lemma S2673_c_ne_zero (PR : Ideal R) [PR.IsMaximal]
    (e : R ⧸ PR ≃+* ZMod 1249) :
    (Ideal.Quotient.mk PR) ((((S2660u)⁻¹ : Rˣ) : R)) * e.symm 415 ≠ 0 := by
  have h1 : IsUnit ((Ideal.Quotient.mk PR) ((((S2660u)⁻¹ : Rˣ) : R))) :=
    (((S2660u)⁻¹ : Rˣ).isUnit).map (Ideal.Quotient.mk PR).toMonoidHom
  have h2 : e.symm (415 : ZMod 1249) ≠ 0 := by
    intro h
    have hc := congrArg e h
    rw [RingEquiv.apply_symm_apply, map_zero] at hc
    exact (by decide : (415 : ZMod 1249) ≠ 0) hc
  exact mul_ne_zero h1.ne_zero h2

lemma S2673_f10_factorization (PR : Ideal R) [PR.IsMaximal]
    (e : R ⧸ PR ≃+* ZMod 1249) :
    f10.map (Ideal.Quotient.mk PR) =
      C ((Ideal.Quotient.mk PR) ((((S2660u)⁻¹ : Rˣ) : R)) * e.symm 415) *
        ((S2550F2.map e.symm.toRingHom) * (S2550F10.map e.symm.toRingHom)) := by
  have hc_eq : e.toRingHom ((Ideal.Quotient.mk PR) ((((S2660u)⁻¹ : Rˣ) : R)) * e.symm 415) =
      ((e.toRingHom.comp (Ideal.Quotient.mk PR)) ((((S2660u)⁻¹ : Rˣ) : R))) * 415 := by
    rw [map_mul]
    have h2 : e.toRingHom (e.symm (415 : ZMod 1249)) = 415 :=
      RingEquiv.apply_symm_apply e (415 : ZMod 1249)
    rw [h2]
    rfl
  have hR : (C ((Ideal.Quotient.mk PR) ((((S2660u)⁻¹ : Rˣ) : R)) * e.symm 415) *
        ((S2550F2.map e.symm.toRingHom) * (S2550F10.map e.symm.toRingHom))).map
          e.toRingHom =
      C (((e.toRingHom.comp (Ideal.Quotient.mk PR)) ((((S2660u)⁻¹ : Rˣ) : R))) * 415) *
        (S2550F2 * S2550F10) := by
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_mul,
      S2673_F2_map_map PR e, S2673_F10_map_map PR e, hc_eq]
  have hL : (f10.map (Ideal.Quotient.mk PR)).map e.toRingHom =
      C (((e.toRingHom.comp (Ideal.Quotient.mk PR)) ((((S2660u)⁻¹ : Rˣ) : R))) * 415) *
        (S2550F2 * S2550F10) := by
    rw [S2673_f10_map_eq PR e, S2673_Psi5_mod, ← mul_assoc, ← Polynomial.C_mul]
  exact Polynomial.map_injective e.toRingHom e.injective (by rw [hL, hR])

/-! ## 5. The factor degrees (general form) -/

theorem S2673F10FactorDegrees_of_equiv (PR : Ideal R) [PR.IsMaximal]
    (e : R ⧸ PR ≃+* ZMod 1249) :
    factorDegrees (f10.map (Ideal.Quotient.mk PR)) = ({2, 10} : Multiset ℕ) := by
  rw [S2673_f10_factorization PR e]
  exact S2671_factorDegrees_of_factors _ (S2673_c_ne_zero PR e) _ _
    (S2673_F2_map_monic PR e) (S2673_F10_map_monic PR e)
    (S2673_F2_map_irreducible PR e) (S2673_F10_map_irreducible PR e)
    (S2673_F2_map_degree PR e) (S2673_F10_map_degree PR e)

/-! ## 6. The concrete prime over 1249 and the closed statement -/

/-- A prime of R = O_{F'}[1/10] over 1249, with residue field ZMod 1249
(S2672Away10Prime1249Actual). -/
noncomputable def PR1249 : Ideal R :=
  Classical.choose
    LeanFormal.IUT.XiFPaper.S2672Away10Prime1249Actual.S2672_prime1249_away10

theorem PR1249_spec :
    PR1249.IsPrime ∧
      PR1249.LiesOver (Ideal.span ({(1249 : ℤ)} : Set ℤ)) ∧
        Nonempty (R ⧸ PR1249 ≃+* ZMod 1249) :=
  Classical.choose_spec
    LeanFormal.IUT.XiFPaper.S2672Away10Prime1249Actual.S2672_prime1249_away10

theorem PR1249_prime : PR1249.IsPrime := PR1249_spec.1

theorem PR1249_lies :
    PR1249.LiesOver (Ideal.span ({(1249 : ℤ)} : Set ℤ)) := PR1249_spec.2.1

/-- The residue isomorphism R / PR1249 =+* ZMod 1249. -/
noncomputable def e1249 : R ⧸ PR1249 ≃+* ZMod 1249 :=
  Classical.choice PR1249_spec.2.2

theorem PR1249_isMaximal : PR1249.IsMaximal := by
  haveI hfield : IsField (R ⧸ PR1249) :=
    MulEquiv.isField (Field.toIsField (ZMod 1249)) e1249.toMulEquiv
  exact Ideal.Quotient.maximal_of_isField PR1249 hfield

attribute [local instance] PR1249_isMaximal

/-- The reduction of the localised psi_5 model f10 modulo the prime PR1249 of
R = O_{F'}[1/10] over 1249 has irreducible factor degrees {2, 10}. -/
theorem S2673F10FactorDegrees :
    factorDegrees (f10.map (Ideal.Quotient.mk PR1249)) = ({2, 10} : Multiset ℕ) :=
  S2673F10FactorDegrees_of_equiv PR1249 e1249

/-- Bundled form: there is a prime PR of R = O_{F'}[1/10] over 1249 with
residue field ZMod 1249 (S2672) such that f10 mod PR has factor degrees {2, 10}. -/
theorem S2673F10FactorDegrees_away10 :
    ∃ (PR : Ideal R) (hmax : PR.IsMaximal),
      PR.IsPrime ∧ PR.LiesOver (Ideal.span ({(1249 : ℤ)} : Set ℤ)) ∧
        Nonempty (R ⧸ PR ≃+* ZMod 1249) ∧
          @factorDegrees (R ⧸ PR) (@Ideal.Quotient.field R _ PR hmax)
            (f10.map (Ideal.Quotient.mk PR)) = ({2, 10} : Multiset ℕ) := by
  obtain ⟨PR, hprime, hlies, ⟨e⟩⟩ :=
    LeanFormal.IUT.XiFPaper.S2672Away10Prime1249Actual.S2672_prime1249_away10
  haveI hfield : IsField (R ⧸ PR) :=
    MulEquiv.isField (Field.toIsField (ZMod 1249)) e.toMulEquiv
  have hmax : PR.IsMaximal := Ideal.Quotient.maximal_of_isField PR hfield
  haveI : PR.IsMaximal := hmax
  exact ⟨PR, hmax, hprime, hlies, ⟨e⟩, S2673F10FactorDegrees_of_equiv PR e⟩

#check S2673F10FactorDegrees_of_equiv
#check S2673F10FactorDegrees
#check S2673F10FactorDegrees_away10
#print axioms S2673F10FactorDegrees_of_equiv
#print axioms S2673F10FactorDegrees
#print axioms S2673F10FactorDegrees_away10

end LeanFormal.IUT.XiFPaper.S2673F10FactorDegreesActual
end
