/-
S2676: from the localized orbit-size theorem at 1249 to the range cycle-type
requirement S2203RangeCycleTypeRequired S1982Basis.

The orbit-size multiset {2, 10} of the arithmetic Frobenius at p1249R on the
roots of f10' in L is transported to the twelve division roots over F'
(via S2653/S2132) and to the non-monic integral model 2^36 psi_5, and then
fed into S2655RangeTransport.

No sorry, axiom, True/PUnit or native_decide is used.
-/
import tmp.sheaf.xif.paper.S2675LocalizedOrbit1249Actual
import tmp.sheaf.xif.paper.S2655NonmonicRangeActual
import tmp.sheaf.xif.paper.S2653DedekindToRangeActual
import tmp.sheaf.xif.paper.S2132FrobCycleActual

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
open LeanFormal.IUT.XiFPaper.S2675LocalizedOrbit1249Actual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2653DedekindToRangeActual
open LeanFormal.IUT.XiFPaper.S2655NonmonicRangeActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual

namespace LeanFormal.IUT.XiFPaper.S2676RangeCycleType1249Actual

attribute [local instance] Ideal.Quotient.field

abbrev A : Type := S2537ConcreteLocalizationActual.A
abbrev R10 : Type := S2537ConcreteLocalizationActual.R
abbrev T10 : Type := S2537ConcreteLocalizationActual.S
abbrev OL : Type := S2537ConcreteLocalizationActual.C
abbrev K : Type := S2537ConcreteLocalizationActual.K
abbrev L10 : Type := S2537ConcreteLocalizationActual.L
abbrev O : Type := RingOfIntegers S1720Field

lemma S2676_rootPermR_apply_val (sigma : Gal(L10/K))
    (x : (f10'.map (algebraMap R10 K)).rootSet L10) :
    (S2532LocalizedDefinitionsActual.rootPermR R10 K L10 f10'
      S2598bHsepSplitActual.S2598b_hsplit sigma x).1 = sigma x.1 := by
  simp only [S2532LocalizedDefinitionsActual.rootPermR, MulAction.toPermHom_apply,
    MulAction.toPerm_apply, Polynomial.rootSet.coe_smul, AlgEquiv.smul_def]

/-- Relabelling the localized root permutation along the scalar multiple
psi_5 gives the actual division-root permutation. -/
theorem S2676_permCongr_rootPermR (sigma : Gal(L10/K)) :
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
  rw [S2676_rootPermR_apply_val]
  rfl

/-- The orbit-size multiset of the division-root permutation is {2, 10}. -/
theorem S2676_orbitSizeMultiset_divisionRootEquiv (sigma : Gal(L10/K))
    (hcyc : S2217DedekindFrobTheoremActual.orbitSizeMultiset
      (S2532LocalizedDefinitionsActual.rootPermR R10 K L10 f10'
        S2598bHsepSplitActual.S2598b_hsplit sigma) = ({2, 10} : Multiset ℕ)) :
    S2217DedekindFrobTheoremActual.orbitSizeMultiset
      (S2132DivisionRootEquiv sigma) = ({2, 10} : Multiset ℕ) := by
  rw [← S2676_permCongr_rootPermR sigma,
    S2673LocalizedOrbitSizeActual.S2673_orbitSizeMultiset_permCongr,
    hcyc]

/-! ## 2. The non-monic integral model 2^36 psi_5 -/

/-- The non-monic integral model of psi_5 used for the range transport. -/
def f0 : O[X] := S2132Psi5Z.map (Int.castRingHom O)

theorem S2676_hq : f0.map (algebraMap O K) =
    Polynomial.C ((2 : K) ^ 36) * S2057Psi5F := by
  show (S2132Psi5Z.map (Int.castRingHom O)).map (algebraMap O K) = _
  rw [Polynomial.map_map]
  have hcomp : (algebraMap O K).comp (Int.castRingHom O) = Int.castRingHom K := by
    ext z
    simp
  rw [hcomp, S2003Psi5Z_map_K]

theorem S2676_hsplit : (f0.map (algebraMap O L10)).Splits := by
  have h2 : f0.map (algebraMap O L10) =
      (f0.map (algebraMap O K)).map (algebraMap K L10) := by
    rw [Polynomial.map_map, IsScalarTower.algebraMap_eq O K L10]
  rw [h2, S2676_hq, Polynomial.map_mul, Polynomial.map_C]
  exact Polynomial.Splits.C_mul
    (Polynomial.SplittingField.splits (f := S2057Psi5F)) _

/-- The orbit-size multiset of the non-monic integral model is {10, 2}. -/
theorem S2676_orbitSizeMultiset_f0 (sigma : Gal(L10/K))
    (hdiv : S2217DedekindFrobTheoremActual.orbitSizeMultiset
      (S2132DivisionRootEquiv sigma) = ({2, 10} : Multiset ℕ)) :
    S2217DedekindFrobTheoremActual.orbitSizeMultiset
      (rootPerm K L10 f0 S2676_hsplit sigma) = ({10, 2} : Multiset ℕ) := by
  have h := S2653permCongr_rootPerm_eq_divisionRootEquiv (f := f0)
    (hsplit := S2676_hsplit) (σ := sigma) (c := (2 : K) ^ 36) (by norm_num) S2676_hq
  have hcongr : S2217DedekindFrobTheoremActual.orbitSizeMultiset
      ((S2653rootSetEquiv (K := K) (A := L10) (p := S2057Psi5F)
        (q := f0.map (algebraMap O K)) (c := (2 : K) ^ 36) (by norm_num)
        S2676_hq).permCongr (rootPerm K L10 f0 S2676_hsplit sigma)) =
      S2217DedekindFrobTheoremActual.orbitSizeMultiset
        (S2132DivisionRootEquiv sigma) := by
    rw [h]
  calc S2217DedekindFrobTheoremActual.orbitSizeMultiset
        (rootPerm K L10 f0 S2676_hsplit sigma)
      = S2217DedekindFrobTheoremActual.orbitSizeMultiset
          ((S2653rootSetEquiv (K := K) (A := L10) (p := S2057Psi5F)
            (q := f0.map (algebraMap O K)) (c := (2 : K) ^ 36) (by norm_num)
            S2676_hq).permCongr (rootPerm K L10 f0 S2676_hsplit sigma)) :=
        (S2673LocalizedOrbitSizeActual.S2673_orbitSizeMultiset_permCongr _ _).symm
    _ = S2217DedekindFrobTheoremActual.orbitSizeMultiset
          (S2132DivisionRootEquiv sigma) := hcongr
    _ = ({10, 2} : Multiset ℕ) := by rw [hdiv]; decide

/-! ## 3. The range transport -/

/-- The localized orbit-size data at 1249 yields the range cycle-type
requirement. -/
theorem S2676_rangeCycleType102_of_localized (sigma : Gal(L10/K))
    (hcyc : S2217DedekindFrobTheoremActual.orbitSizeMultiset
      (S2532LocalizedDefinitionsActual.rootPermR R10 K L10 f10'
        S2598bHsepSplitActual.S2598b_hsplit sigma) = ({2, 10} : Multiset ℕ)) :
    S2203RangeCycleTypeRequired S1982Basis :=
  S2655RangeTransport f0 S2676_hsplit sigma (c := (2 : K) ^ 36) (by norm_num) S2676_hq
    (S2676_orbitSizeMultiset_f0 sigma
      (S2676_orbitSizeMultiset_divisionRootEquiv sigma hcyc))

/-- **The range cycle-type requirement** from the localized orbit-size theorem
at 1249: there is a prime P of T10 over p1249R and an arithmetic Frobenius at
P whose root orbits at 1249 have sizes 10 and 2, hence the mod-5 range has
cycle type (10, 2). -/
theorem S2676_rangeCycleType102 : S2203RangeCycleTypeRequired S1982Basis := by
  obtain ⟨P, sigma, hP, hPover, H, hcyc⟩ := S2675_exists_localized_orbitSize_1249
  exact S2676_rangeCycleType102_of_localized sigma hcyc

end LeanFormal.IUT.XiFPaper.S2676RangeCycleType1249Actual
end
