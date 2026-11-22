/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/

import tmp.sheaf.xif.paper.S2673LocalizedOrbitSizeActual
import tmp.sheaf.xif.paper.S2667PermBarCycleActual
import tmp.sheaf.xif.paper.S2665P10FintypeActual
import tmp.sheaf.xif.paper.S2581S2543ParamsActual
import tmp.sheaf.xif.paper.S2598bHsepSplitActual
import tmp.sheaf.xif.paper.S2653DedekindToRangeActual
import tmp.sheaf.xif.paper.S2470PairTransitiveFinalActual
import tmp.sheaf.xif.paper.S2510AbsoluteLiftActual
import tmp.sheaf.xif.paper.S2520RootCycleTransferActual
import tmp.sheaf.xif.paper.S2501MatrixPairEquivActual
import tmp.sheaf.xif.paper.S2440RangePairTransitiveSubagentActual

/-!
# S2600: the actual twelve-cycle and the D5 pair-transitivity target

This file closes the final D5 residue step unconditionally:

* S2600_localized_orbitSize_twelve: the arithmetic Frobenius at the actual
  degree-one prime P10 W of the localised 5-division ring T10 = O_L[1/10]
  acts on the roots of the localised monic model f10' with orbit-size
  multiset {12}.
* S2600_divisionRootEquiv_cycleType_twelve: consequently some
  F'-automorphism of the actual splitting field L = F'(E[5]) acts on the
  twelve actual roots of psi_5 with cycle type {12}.
* S2600_twelveCycleInput: the literal S2440TwelveCycleInputRequired.
* S2600Target: the literal S2470Target.

No sorry, axiom, native_decide or True is used.
-/

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual

namespace LeanFormal.IUT.XiFPaper.S2600D5FinalResidueActual

attribute [local instance] Ideal.Quotient.field

abbrev A : Type := LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.A
abbrev R10 : Type := LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.R
abbrev T10 : Type := LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.S
abbrev K : Type := LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.K
abbrev L10 : Type := LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.L
abbrev M : Submonoid A := LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.M

abbrev f : R10[X] := LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.f10'
abbrev p : Ideal R10 := LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.p10
abbrev P : Ideal T10 := LeanFormal.IUT.XiFPaper.S2663P10PrimeActual.P10
  LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.W

/-! ## 1. The Frobenius instance and the orbit-size computation -/

local instance hp : p.IsMaximal :=
  LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.p10_max
local instance hPprime : P.IsPrime :=
  LeanFormal.IUT.XiFPaper.S2581S2543ParamsActual.P10_prime_self
local instance hPover : P.LiesOver p :=
  LeanFormal.IUT.XiFPaper.S2581S2543ParamsActual.P10_lies_p10_self
local instance hPmax : P.IsMaximal :=
  LeanFormal.IUT.XiFPaper.S2581S2543ParamsActual.P10_isMaximal_self
local instance fintypeR10p : Fintype (R10 ⧸ p) :=
  LeanFormal.IUT.XiFPaper.S2581S2543ParamsActual.fintype_quot_p10
local instance decEqR10p : DecidableEq (R10 ⧸ p) :=
  LeanFormal.IUT.XiFPaper.S2581S2543ParamsActual.decEq_quot_p10
local instance fintypeT10P : Fintype (T10 ⧸ P) :=
  LeanFormal.IUT.XiFPaper.S2665P10FintypeActual.P10_fintype
    LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.W
local instance decEqT10P : DecidableEq (T10 ⧸ P) := Classical.decEq _

/-- The fraction-ring structure of the localised base ring. -/
local instance isFractionRingR10K : IsFractionRing R10 K :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (M := M) R10 K

theorem f_natDegree_ne_zero : f.natDegree ≠ 0 := by
  rw [show f.natDegree = 12 from
    LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.f10'_natDegree]
  norm_num

theorem f_hsepK : (f.map (algebraMap R10 K)).Separable := by
  rw [show f.map (algebraMap R10 K) =
      Polynomial.C ((5 : K)⁻¹) * LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual.S2057Psi5F from
    LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.f10'_map_scalar]
  exact Polynomial.Separable.unit_mul
    (isUnit_C.mpr (isUnit_iff_ne_zero.mpr
      (inv_ne_zero (by norm_num : (5 : K) ≠ 0))))
    LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual.S2057Psi5F_separable

/-- The factor degrees of the reduction of the localised model at p10. -/
theorem factorDegrees_fbar :
    LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual.factorDegrees
      (LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual.fbar f p) =
        ({12} : Multiset ℕ) := by
  classical
  change LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual.factorDegrees
    (LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.fbar10) = ({12} : Multiset ℕ)
  unfold LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual.factorDegrees
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible
    LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.fbar10_irreducible,
    Monic.normalize_eq_self
      LeanFormal.IUT.XiFPaper.S2667PermBarCycleActual.fbar10_monic]
  simp [LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.fbar10_natDegree]

/-- The localized Dedekind--Frobenius orbit-size theorem at the actual
degree-one prime P10 W: some arithmetic Frobenius has orbit-size multiset
{12} on the roots of the localised monic model. -/
theorem localized_orbitSize_twelve :
    ∃ sigma : Gal(L10/K),
      IsArithFrobAt R10 sigma P ∧
        LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual.orbitSizeMultiset
          (LeanFormal.IUT.XiFPaper.S2532LocalizedDefinitionsActual.rootPermR
            R10 K L10 f
            LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hsplit sigma) =
          ({12} : Multiset ℕ) := by
  classical
  haveI hInv : Algebra.IsInvariant R10 T10 Gal(L10/K) :=
    Algebra.isInvariant_of_isGalois R10 K L10 T10
  obtain ⟨sigma, H⟩ :=
    IsArithFrobAt.exists_of_isInvariant (S := T10) R10 (Gal(L10/K)) P
  refine ⟨sigma, H, ?_⟩
  rw [LeanFormal.IUT.XiFPaper.S2673LocalizedOrbitSizeActual.S2673_localized_orbitSizeMultiset_eq_factorDegrees
    (f := f) (p := p) (P := P)
    LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hmonic
    LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hsep
    LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hsplit
    f_natDegree_ne_zero f_hsepK sigma H,
    factorDegrees_fbar]

/-! ## 2. From the orbit-size multiset to the division-root twelve-cycle -/

/-- The value of the localized root permutation. -/
theorem rootPermR_apply_val (sigma : Gal(L10/K))
    (x : (f.map (algebraMap R10 K)).rootSet L10) :
    (LeanFormal.IUT.XiFPaper.S2532LocalizedDefinitionsActual.rootPermR
      R10 K L10 f
      LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hsplit sigma x).1 =
        sigma x.1 := by
  simp only [LeanFormal.IUT.XiFPaper.S2532LocalizedDefinitionsActual.rootPermR,
    MulAction.toPermHom_apply, MulAction.toPerm_apply, Polynomial.rootSet.coe_smul,
    AlgEquiv.smul_def]

/-- Relabelling the localized root permutation along the nonzero scalar multiple
f10' = C (1/5) * psi_5 gives the actual division-root permutation. -/
theorem permCongr_rootPermR (sigma : Gal(L10/K)) :
    (LeanFormal.IUT.XiFPaper.S2653DedekindToRangeActual.S2653rootSetEquiv
      (K := K) (A := L10)
      (p := LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual.S2057Psi5F)
      (q := f.map (algebraMap R10 K)) (c := (5 : K)⁻¹)
      (inv_ne_zero (by norm_num : (5 : K) ≠ 0))
      LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.f10'_map_scalar).permCongr
      (LeanFormal.IUT.XiFPaper.S2532LocalizedDefinitionsActual.rootPermR
        R10 K L10 f
        LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hsplit sigma) =
      LeanFormal.IUT.XiFPaper.S2132FrobCycleActual.S2132DivisionRootEquiv sigma := by
  ext x
  rw [Equiv.permCongr_apply]
  change
    (LeanFormal.IUT.XiFPaper.S2532LocalizedDefinitionsActual.rootPermR
      R10 K L10 f
      LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hsplit sigma
      ((LeanFormal.IUT.XiFPaper.S2653DedekindToRangeActual.S2653rootSetEquiv
        (K := K) (A := L10)
        (p := LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual.S2057Psi5F)
        (q := f.map (algebraMap R10 K)) (c := (5 : K)⁻¹)
        (inv_ne_zero (by norm_num : (5 : K) ≠ 0))
        LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.f10'_map_scalar).symm x)).1 =
      (LeanFormal.IUT.XiFPaper.S2132FrobCycleActual.S2132DivisionRootEquiv sigma x).1
  rw [rootPermR_apply_val]
  rfl

/-- The orbit-size multiset of the division-root permutation is {12}. -/
theorem orbitSizeMultiset_divisionRootEquiv (sigma : Gal(L10/K))
    (h : LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual.orbitSizeMultiset
      (LeanFormal.IUT.XiFPaper.S2532LocalizedDefinitionsActual.rootPermR
        R10 K L10 f
        LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hsplit sigma) =
        ({12} : Multiset ℕ)) :
    LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual.orbitSizeMultiset
      (LeanFormal.IUT.XiFPaper.S2132FrobCycleActual.S2132DivisionRootEquiv sigma) =
        ({12} : Multiset ℕ) := by
  rw [← permCongr_rootPermR sigma,
    LeanFormal.IUT.XiFPaper.S2673LocalizedOrbitSizeActual.S2673_orbitSizeMultiset_permCongr,
    h]

/-- A permutation whose orbit-size multiset is {12} is a twelve-cycle. -/
theorem cycleType_of_orbitSize_twelve {α : Type*} [Fintype α]
    (sigma : Equiv.Perm α)
    (h : LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual.orbitSizeMultiset sigma =
      ({12} : Multiset ℕ)) :
    @Equiv.Perm.cycleType α _ (Classical.decEq α) sigma =
      ({12} : Multiset ℕ) := by
  classical
  have hfilt_rep :
      (Multiset.replicate (Fintype.card (Function.fixedPoints sigma)) 1).filter
        (fun x => x ≠ 1) = 0 := by
    induction Fintype.card (Function.fixedPoints sigma) with
    | zero => simp
    | succ n ih => simp [Multiset.replicate_succ, ih]
  have hfilter : (sigma.cycleType.filter (fun x => x ≠ 1)) =
      ({12} : Multiset ℕ) := by
    have hc := congrArg (fun m : Multiset ℕ => m.filter (fun n => n ≠ 1)) h
    simp only [LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual.orbitSizeMultiset,
      Multiset.filter_add, hfilt_rep, add_zero] at hc
    rwa [show Multiset.filter (fun n => n ≠ 1) ({12} : Multiset ℕ) =
      ({12} : Multiset ℕ) from by decide] at hc
  have hcount1 : sigma.cycleType.count 1 = 0 := by
    have hle : sigma.cycleType ≤
        LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual.orbitSizeMultiset sigma :=
      Multiset.le_add_right _ _
    have hcnt :
        (LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual.orbitSizeMultiset sigma).count 1 = 0 := by
      rw [h]
      decide
    have := Multiset.count_le_of_le (1 : ℕ) hle
    rw [hcnt] at this
    exact Nat.eq_zero_of_le_zero this
  have hsplit :=
    LeanFormal.IUT.XiFPaper.S2673LocalizedOrbitSizeActual.S2673_filter_ne_one_add_replicate_count_one
      sigma.cycleType
  rw [hcount1, Multiset.replicate_zero, add_zero] at hsplit
  rw [← hsplit, hfilter]

/-- Some F'-automorphism of the actual splitting field acts on the twelve
roots of psi_5 with cycle type {12}. -/
theorem divisionRootEquiv_cycleType_twelve :
    ∃ sigma : Gal(L10/K),
      Equiv.Perm.cycleType
        (LeanFormal.IUT.XiFPaper.S2132FrobCycleActual.S2132DivisionRootEquiv
          sigma) = ({12} : Multiset ℕ) := by
  obtain ⟨sigma, -, horbit⟩ := localized_orbitSize_twelve
  exact ⟨sigma,
    cycleType_of_orbitSize_twelve _
      (orbitSizeMultiset_divisionRootEquiv sigma horbit)⟩

/-! ## 3. The unconditional S2440 twelve-cycle input and the S2470 target -/

/-- **Unconditional S2440 twelve-cycle input.** -/
theorem S2600_twelveCycleInput :
    LeanFormal.IUT.XiFPaper.S2440RangePairTransitiveSubagentActual.S2440TwelveCycleInputRequired := by
  obtain ⟨sigma, hcyc⟩ := divisionRootEquiv_cycleType_twelve
  obtain ⟨tau, htau⟩ :=
    LeanFormal.IUT.XiFPaper.S2510AbsoluteLiftActual.S2510_exists_lift sigma
  refine ⟨S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis tau,
    MonoidHom.mem_range.mpr ⟨tau, rfl⟩, ?_⟩
  rw [LeanFormal.IUT.XiFPaper.S2501MatrixPairEquivActual.S2501PairMatrix_cycleType tau]
  rw [← LeanFormal.IUT.XiFPaper.S2520RootCycleTransferActual.S2520cycleType_eq
    sigma tau htau]
  exact hcyc

/-- **Unconditional S2470 target.** -/
theorem S2600Target :
    LeanFormal.IUT.XiFPaper.S2470PairTransitiveFinalActual.S2470Target :=
  LeanFormal.IUT.XiFPaper.S2470PairTransitiveFinalActual.S2470Target_of_twelveCycle
    S2600_twelveCycleInput

#print axioms localized_orbitSize_twelve
#print axioms factorDegrees_fbar
#print axioms permCongr_rootPermR
#print axioms orbitSizeMultiset_divisionRootEquiv
#print axioms cycleType_of_orbitSize_twelve
#print axioms divisionRootEquiv_cycleType_twelve
#print axioms S2600_twelveCycleInput
#print axioms S2600Target

end LeanFormal.IUT.XiFPaper.S2600D5FinalResidueActual
end