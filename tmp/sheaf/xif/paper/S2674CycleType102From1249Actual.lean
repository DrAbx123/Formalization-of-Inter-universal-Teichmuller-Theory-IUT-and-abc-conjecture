/-
S2674: assembly of HasCycleType102 from the actual mod-1249 factor certificate.

This file is the requested independent assembly file
  tmp/sheaf/xif/paper/S2674CycleType102From1249Actual.lean
and does not modify any existing source file.

What is used (all actual, unconditional):
* the actual degree-one prime p1249A of A = O_{F'} over 1249 and its localisation
  p1249R in R = O_{F'}[1/10] with residue field ZMod 1249 (S2669/S2674);
* the exact explicit factorisation f10' mod p1249R = C 415 * (F2 * F10) from the
  S2550 certificate, transported along the residue isomorphism (S2671/S2674),
  giving factorDegrees (f10' mod p1249R) = {2, 10};
* the localized Dedekind--Frobenius orbit-size theorem S2673 for the monic
  localized model f10' (this is the honest replacement for the non-monic model
  over O_{F'}, see the note below);
* the non-monic range transport S2655, whose conclusion
  S2203RangeCycleTypeRequired S1982Basis is definitionally
  HasCycleType102 of the actual mod-5 range.

A note on the originally suggested direct route through S2445: it is not
available.  The integer model S2132Psi5Z satisfies
S2132Psi5Z.map (Int.castRingHom Q) = C (2^36) * S2057Psi5Q (S2003), and its
leading coefficient is 5 * 2^36, so any f : O_{F'}[X] with
f.map (algebraMap O_{F'} F') = C c * S2057Psi5F for a unit c has leading
coefficient 5 * 2^36 (up to units) and hence is never monic; the monic
normalisation S2057Psi5F / 5 does not have integral coefficients (its x^10
coefficient is -7322650804224 / (5 * 2^36), compare the denominator argument of
S2132NoIntegerModel).  Thus the hmonic hypothesis of S2445 cannot be met for the
division polynomial, and the assembly must pass through the localized monic
model f10' as done here.

No sorry, axiom, True/PUnit or native_decide is used.
-/
import tmp.sheaf.xif.paper.S2674LocalizedOrbitSize1249Actual
import tmp.sheaf.xif.paper.S2673LocalizedOrbitSizeActual
import tmp.sheaf.xif.paper.S2655NonmonicRangeActual
import tmp.sheaf.xif.paper.S2653DedekindToRangeActual
import tmp.sheaf.xif.paper.S2132FrobCycleActual
import tmp.sheaf.xif.paper.S2598bHsepSplitActual
import tmp.sheaf.xif.paper.S2550TwoFactorCertificateActual
import tmp.sheaf.xif.paper.S2671Mod1249FactorDegreesActual

noncomputable section
set_option maxHeartbeats 32000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2577Away10FbarActual
open LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual
open LeanFormal.IUT.XiFPaper.S2674LocalizedOrbitSize1249Actual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2653DedekindToRangeActual
open LeanFormal.IUT.XiFPaper.S2655NonmonicRangeActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S2592GenericLocalizedResidueIsoActual
open LeanFormal.IUT.XiFPaper.S2671Mod1249FactorDegreesActual
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual

namespace LeanFormal.IUT.XiFPaper.S2674CycleType102From1249Actual

attribute [local instance] Ideal.Quotient.field

abbrev A : Type := S2537ConcreteLocalizationActual.A
abbrev R10 : Type := S2537ConcreteLocalizationActual.R
abbrev T10 : Type := S2537ConcreteLocalizationActual.S
abbrev OL : Type := S2537ConcreteLocalizationActual.C
abbrev K : Type := S2537ConcreteLocalizationActual.K
abbrev L10 : Type := S2537ConcreteLocalizationActual.L
abbrev O : Type := RingOfIntegers S1720Field

local instance : Fact (Nat.Prime 1249) := ⟨by norm_num⟩

/-! ## 1. The reduction of f10' modulo p1249R is separable -/

/-- The explicit mod-1249 product C 415 * (F2 * F10) is separable. -/
theorem S2674C_separable_psiZ :
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
      ({S2550F2, S2550F10} : Multiset (ZMod 1249)[X]) := by
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
    have h2 : (2 : Nat) = 10 := by
      rw [<- S2671F2_degree, <- S2671F10_degree, h]
    norm_num at h2
  rw [show ({S2550F2, S2550F10} : Multiset (ZMod 1249)[X]) =
      S2550F2 ::ₘ S2550F10 ::ₘ 0 from by
    simp [Multiset.insert_eq_cons]]
  simp [Multiset.nodup_cons, hne]

/-- The reduction of the localized model f10' modulo p1249R is separable. -/
theorem S2674C_hsep : (fbar f10' p1249R).Separable := by
  refine (Polynomial.separable_map residueEquivR1249.toRingHom).mp ?_
  rw [S2674_fbar_map_eq, <- S2550Psi5Mod1249_eq, S2550Product]
  exact Polynomial.Separable.unit_mul
    (isUnit_C.mpr (u_isUnit.map (residueEquivR1249.toRingHom.comp
      (Ideal.Quotient.mk p1249R)).toMonoidHom))
    S2674C_separable_psiZ

theorem S2674C_f10'_natDegree_ne_zero : f10'.natDegree ≠ 0 := by
  rw [f10'_natDegree]
  norm_num

theorem S2674C_f10'_hsepK : (f10'.map (algebraMap R10 K)).Separable := by
  rw [show f10'.map (algebraMap R10 K) =
      Polynomial.C ((5 : K)⁻¹) * S2057Psi5F from f10'_map_scalar]
  exact Polynomial.Separable.unit_mul
    (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by norm_num)))
    S2057Psi5F_separable

/-! ## 2. The residue field of a prime of T10 over p1249R -/

theorem S2674C_int1249_mem_T10 (P : Ideal T10) [hPover : P.LiesOver p1249R] :
    algebraMap Int T10 (1249 : Int) ∈ P := by
  have hmem : algebraMap Int R10 (1249 : Int) ∈ P.under R10 := by
    rw [show P.under R10 = p1249R from hPover.over.symm]
    exact S2674_int1249_mem_p1249R
  have htop : algebraMap R10 T10 (algebraMap Int R10 (1249 : Int)) ∈ P :=
    Ideal.mem_comap.mp hmem
  have h1 : algebraMap Int R10 (1249 : Int) = (1249 : R10) := map_intCast _ _
  have h2 : algebraMap Int T10 (1249 : Int) = (1249 : T10) := map_intCast _ _
  have h3 : algebraMap R10 T10 (1249 : R10) = (1249 : T10) := map_natCast _ _
  rw [h2, <- h3, <- h1]
  exact htop

theorem S2674C_under_OL_ne_bot (P : Ideal T10) [hP : P.IsPrime]
    [hPover : P.LiesOver p1249R] : P.under OL ≠ ⊥ := by
  intro hbot
  have h1249T : algebraMap Int T10 (1249 : Int) ∈ P := S2674C_int1249_mem_T10 P
  have hmem : algebraMap Int OL (1249 : Int) ∈ P.under OL := by
    rw [Ideal.under_def, Ideal.mem_comap]
    have h1 : algebraMap Int OL (1249 : Int) = (1249 : OL) := map_intCast _ _
    have h2 : algebraMap Int T10 (1249 : Int) = (1249 : T10) := map_intCast _ _
    have h3 : algebraMap OL T10 (1249 : OL) = (1249 : T10) := map_natCast _ _
    rw [h1, h3, <- h2]
    exact h1249T
  rw [hbot] at hmem
  have hne' : (1249 : L10) ≠ 0 := by norm_num
  have hne : algebraMap Int OL (1249 : Int) ≠ 0 := by
    intro h0
    apply hne'
    have h1 := congrArg (algebraMap OL L10) h0
    rw [map_zero, <- IsScalarTower.algebraMap_apply Int OL L10] at h1
    rw [show algebraMap Int L10 (1249 : Int) = (1249 : L10) from by norm_num] at h1
    exact h1
  exact hne (Ideal.mem_bot.mp hmem)

theorem S2674C_under_OL_max (P : Ideal T10) [hP : P.IsPrime]
    [hPover : P.LiesOver p1249R] : (P.under OL).IsMaximal := by
  haveI hfin : Finite (OL ⧸ P.under OL) :=
    Ring.HasFiniteQuotients.finiteQuotient (S2674C_under_OL_ne_bot P)
  haveI : IsDomain (OL ⧸ P.under OL) := Ideal.Quotient.isDomain (P.under OL)
  exact Ideal.Quotient.maximal_of_isField (P.under OL)
    (Finite.isField_of_domain (OL ⧸ P.under OL))

noncomputable def S2674C_residueEquiv (P : Ideal T10) [hP : P.IsPrime]
    [hPover : P.LiesOver p1249R] :
    (OL ⧸ P.under OL) ≃+* (T10 ⧸ P) :=
  letI := S2674C_under_OL_max P
  localizedResidueEquiv
    (R := OL) (T := T10)
    (M := Algebra.algebraMapSubmonoid OL (Submonoid.powers (10 : A)))
    (I := P.under OL) (P := P) rfl

noncomputable instance S2674C_fintype_quot (P : Ideal T10) [hP : P.IsPrime]
    [hPover : P.LiesOver p1249R] : Fintype (T10 ⧸ P) := by
  haveI hfin : Finite (OL ⧸ P.under OL) :=
    Ring.HasFiniteQuotients.finiteQuotient (S2674C_under_OL_ne_bot P)
  haveI : Fintype (OL ⧸ P.under OL) := Fintype.ofFinite _
  exact Fintype.ofEquiv (OL ⧸ P.under OL) (S2674C_residueEquiv P)

instance S2674C_decEq_quot (P : Ideal T10) [hP : P.IsPrime]
    [hPover : P.LiesOver p1249R] : DecidableEq (T10 ⧸ P) := Classical.decEq _

/-! ## 3. The localized orbit-size theorem at p1249R -/

/-- For every prime P of T10 over p1249R there is an arithmetic Frobenius at P
whose orbit-size multiset on the roots of f10' is 2 and 10. -/
theorem S2674C_localized_orbitSize (P : Ideal T10) [hP : P.IsPrime]
    [hPover : P.LiesOver p1249R] :
    ∃ sigma : Gal(L10/K), IsArithFrobAt R10 sigma P ∧
      S2217DedekindFrobTheoremActual.orbitSizeMultiset
        (S2532LocalizedDefinitionsActual.rootPermR R10 K L10 f10'
          S2598bHsepSplitActual.S2598b_hsplit sigma) = ({2, 10} : Multiset Nat) := by
  classical
  haveI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (p := p1249R) (P := P)
  haveI : Fintype (T10 ⧸ P) := S2674C_fintype_quot P
  haveI hInv : Algebra.IsInvariant R10 T10 Gal(L10/K) :=
    Algebra.isInvariant_of_isGalois R10 K L10 T10
  obtain ⟨sigma, H⟩ := IsArithFrobAt.exists_of_isInvariant (S := T10) R10 (Gal(L10/K)) P
  refine ⟨sigma, H, ?_⟩
  rw [S2673LocalizedOrbitSizeActual.S2673_localized_orbitSizeMultiset_eq_factorDegrees
    (f := f10') (p := p1249R) (P := P)
    S2598bHsepSplitActual.S2598b_hmonic S2674C_hsep
    S2598bHsepSplitActual.S2598b_hsplit S2674C_f10'_natDegree_ne_zero
    S2674C_f10'_hsepK sigma H,
    S2674LocalizedOrbitSize1249Actual.S2674_factorDegrees_fbar]

/-- Existence form: a prime of T10 over p1249R and a Frobenius at it with
orbit-size multiset 2 and 10. -/
theorem S2674C_exists_localized_orbitSize :
    ∃ (P : Ideal T10) (sigma : Gal(L10/K)),
      P.IsPrime ∧ P.LiesOver p1249R ∧ IsArithFrobAt R10 sigma P ∧
      S2217DedekindFrobTheoremActual.orbitSizeMultiset
        (S2532LocalizedDefinitionsActual.rootPermR R10 K L10 f10'
          S2598bHsepSplitActual.S2598b_hsplit sigma) = ({2, 10} : Multiset Nat) := by
  obtain ⟨P, hPmax, hPover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := R10) (S := T10) p1249R
  haveI : P.IsMaximal := hPmax
  haveI : P.IsPrime := hPmax.isPrime
  haveI : P.LiesOver p1249R := hPover
  obtain ⟨sigma, H, hcyc⟩ := S2674C_localized_orbitSize P
  exact ⟨P, sigma, hPmax.isPrime, hPover, H, hcyc⟩

/-! ## 4. The non-monic integral model 2^36 psi_5 -/

def f0 : O[X] := S2132Psi5Z.map (Int.castRingHom O)

theorem S2674C_hq : f0.map (algebraMap O K) =
    Polynomial.C ((2 : K) ^ 36) * S2057Psi5F := by
  show (S2132Psi5Z.map (Int.castRingHom O)).map (algebraMap O K) = _
  rw [Polynomial.map_map]
  have hcomp : (algebraMap O K).comp (Int.castRingHom O) = Int.castRingHom K := by
    ext z
    simp
  rw [hcomp, S2003Psi5Z_map_K]

theorem S2674C_hsplit : (f0.map (algebraMap O L10)).Splits := by
  have h2 : f0.map (algebraMap O L10) =
      (f0.map (algebraMap O K)).map (algebraMap K L10) := by
    rw [Polynomial.map_map, IsScalarTower.algebraMap_eq O K L10]
  rw [h2, S2674C_hq, Polynomial.map_mul, Polynomial.map_C]
  exact Polynomial.Splits.C_mul
    (Polynomial.SplittingField.splits (f := S2057Psi5F)) _
/-- The concrete non-monic obstruction: the integer model f0 is not monic, so
the hmonic hypothesis of the non-localized Dedekind--Frobenius theorem S2445
cannot be met for the division polynomial.  Its leading coefficient is
5 * 2^36 = 343597383680. -/
theorem S2674C_f0_not_monic : ¬ f0.Monic := by
  intro hmono
  have hleadZ : S2132Psi5Z.leadingCoeff = (343597383680 : Int) := by
    have hdeg : S2132Psi5Z.natDegree = 12 := by
      unfold S2132Psi5Z
      compute_degree!
    rw [show S2132Psi5Z.leadingCoeff = S2132Psi5Z.coeff S2132Psi5Z.natDegree from rfl,
      hdeg]
    unfold S2132Psi5Z
    norm_num [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_pow]
  have hlead0 : f0.leadingCoeff = algebraMap Int O (343597383680 : Int) := by
    unfold f0
    rw [Polynomial.leadingCoeff_map_of_injective (Int.cast_injective), hleadZ]
    rfl
  have hone : algebraMap Int O (343597383680 : Int) = 1 := by
    rw [<- hlead0]
    exact hmono
  have hcomp : (algebraMap O K).comp (Int.castRingHom O) = Int.castRingHom K := by
    ext z
    simp
  haveI hst : IsScalarTower Int O K := IsScalarTower.of_algebraMap_eq' hcomp
  have hK : (343597383680 : K) = 1 := by
    have h := congrArg (algebraMap O K) hone
    rw [map_one, <- IsScalarTower.algebraMap_apply Int O K] at h
    simpa using h
  norm_num at hK

lemma S2674C_rootPermR_apply_val (sigma : Gal(L10/K))
    (x : (f10'.map (algebraMap R10 K)).rootSet L10) :
    (S2532LocalizedDefinitionsActual.rootPermR R10 K L10 f10'
      S2598bHsepSplitActual.S2598b_hsplit sigma x).1 = sigma x.1 := by
  simp only [S2532LocalizedDefinitionsActual.rootPermR, MulAction.toPermHom_apply,
    MulAction.toPerm_apply, Polynomial.rootSet.coe_smul, AlgEquiv.smul_def]

/-- Relabelling the localized root permutation along the scalar multiple
psi_5 gives the actual division-root permutation. -/
theorem S2674C_permCongr_rootPermR (sigma : Gal(L10/K)) :
    (S2653rootSetEquiv (K := K) (A := L10) (p := S2057Psi5F)
        (q := f10'.map (algebraMap R10 K)) (c := (5 : K)⁻¹)
        (inv_ne_zero (by norm_num : (5 : K) ≠ 0)) f10'_map_scalar).permCongr
        (S2532LocalizedDefinitionsActual.rootPermR R10 K L10 f10'
          S2598bHsepSplitActual.S2598b_hsplit sigma) =
      S2132DivisionRootEquiv sigma := by
  ext x
  rw [Equiv.permCongr_apply]
  change (S2532LocalizedDefinitionsActual.rootPermR R10 K L10 f10'
      S2598bHsepSplitActual.S2598b_hsplit sigma
      ((S2653rootSetEquiv (K := K) (A := L10) (p := S2057Psi5F)
        (q := f10'.map (algebraMap R10 K)) (c := (5 : K)⁻¹)
        (inv_ne_zero (by norm_num : (5 : K) ≠ 0)) f10'_map_scalar).symm x)).1 =
    (S2132DivisionRootEquiv sigma x).1
  rw [S2674C_rootPermR_apply_val]
  rfl

/-- The orbit-size multiset of the division-root permutation is 2 and 10. -/
theorem S2674C_orbitSizeMultiset_divisionRootEquiv (sigma : Gal(L10/K))
    (hcyc : S2217DedekindFrobTheoremActual.orbitSizeMultiset
      (S2532LocalizedDefinitionsActual.rootPermR R10 K L10 f10'
        S2598bHsepSplitActual.S2598b_hsplit sigma) = ({2, 10} : Multiset Nat)) :
    S2217DedekindFrobTheoremActual.orbitSizeMultiset
      (S2132DivisionRootEquiv sigma) = ({2, 10} : Multiset Nat) := by
  rw [<- S2674C_permCongr_rootPermR sigma,
    S2673LocalizedOrbitSizeActual.S2673_orbitSizeMultiset_permCongr,
    hcyc]

/-- The orbit-size multiset of the non-monic integral model is 10 and 2. -/
theorem S2674C_orbitSizeMultiset_f0 (sigma : Gal(L10/K))
    (hdiv : S2217DedekindFrobTheoremActual.orbitSizeMultiset
      (S2132DivisionRootEquiv sigma) = ({2, 10} : Multiset Nat)) :
    S2217DedekindFrobTheoremActual.orbitSizeMultiset
      (rootPerm K L10 f0 S2674C_hsplit sigma) = ({10, 2} : Multiset Nat) := by
  have h := S2653permCongr_rootPerm_eq_divisionRootEquiv (f := f0)
    (hsplit := S2674C_hsplit) (σ := sigma) (c := (2 : K) ^ 36) (by norm_num) S2674C_hq
  have hcongr : S2217DedekindFrobTheoremActual.orbitSizeMultiset
      ((S2653rootSetEquiv (K := K) (A := L10) (p := S2057Psi5F)
        (q := f0.map (algebraMap O K)) (c := (2 : K) ^ 36) (by norm_num)
        S2674C_hq).permCongr (rootPerm K L10 f0 S2674C_hsplit sigma)) =
      S2217DedekindFrobTheoremActual.orbitSizeMultiset
        (S2132DivisionRootEquiv sigma) := by
    rw [h]
  calc S2217DedekindFrobTheoremActual.orbitSizeMultiset
        (rootPerm K L10 f0 S2674C_hsplit sigma)
      = S2217DedekindFrobTheoremActual.orbitSizeMultiset
          ((S2653rootSetEquiv (K := K) (A := L10) (p := S2057Psi5F)
            (q := f0.map (algebraMap O K)) (c := (2 : K) ^ 36) (by norm_num)
            S2674C_hq).permCongr (rootPerm K L10 f0 S2674C_hsplit sigma)) :=
        (S2673LocalizedOrbitSizeActual.S2673_orbitSizeMultiset_permCongr _ _).symm
    _ = S2217DedekindFrobTheoremActual.orbitSizeMultiset
          (S2132DivisionRootEquiv sigma) := hcongr
    _ = ({10, 2} : Multiset Nat) := by rw [hdiv]; decide

/-! ## 5. The range transport -/

/-- The localized orbit-size data at 1249 yields the range cycle-type
requirement. -/
theorem S2674C_rangeCycleType102_of_localized (sigma : Gal(L10/K))
    (hcyc : S2217DedekindFrobTheoremActual.orbitSizeMultiset
      (S2532LocalizedDefinitionsActual.rootPermR R10 K L10 f10'
        S2598bHsepSplitActual.S2598b_hsplit sigma) = ({2, 10} : Multiset Nat)) :
    S2203RangeCycleTypeRequired S1982Basis :=
  S2655RangeTransport f0 S2674C_hsplit sigma (c := (2 : K) ^ 36) (by norm_num) S2674C_hq
    (S2674C_orbitSizeMultiset_f0 sigma
      (S2674C_orbitSizeMultiset_divisionRootEquiv sigma hcyc))

/-- The range cycle-type requirement from the actual 1249 factor certificate:
there is a prime P of T10 over p1249R and an arithmetic Frobenius at P whose
root orbits at 1249 have sizes 10 and 2, hence the mod-5 range has cycle type
10 and 2. -/
theorem S2674CycleType102 : S2203RangeCycleTypeRequired S1982Basis := by
  obtain ⟨P, sigma, hP, hPover, H, hcyc⟩ := S2674C_exists_localized_orbitSize
  exact S2674C_rangeCycleType102_of_localized sigma hcyc

/-- The same statement in the unfolded form required by the D5 assembly:
the actual mod-5 range has an element of cycle type 10 and 2 on the twelve
pairs. -/
theorem S2674HasCycleType102 :
    HasCycleType102
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range :=
  S2674CycleType102

#check S2674CycleType102
#check S2674HasCycleType102
#print axioms S2674CycleType102
#print axioms S2674HasCycleType102

end LeanFormal.IUT.XiFPaper.S2674CycleType102From1249Actual
end



