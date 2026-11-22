/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S2673LocalizedOrbitSizeActual
import tmp.sheaf.xif.paper.S2653DedekindToRangeActual
import tmp.sheaf.xif.paper.S2598bHsepSplitActual
import tmp.sheaf.xif.paper.S2581S2543ParamsActual
import tmp.sheaf.xif.paper.S2665P10FintypeActual
import tmp.sheaf.xif.paper.S2663P10PrimeActual
import tmp.sheaf.xif.paper.S2667PermBarCycleActual
import tmp.sheaf.xif.paper.S2532PairTransitiveActual
import tmp.sheaf.xif.paper.S2577Away10FbarActual
import tmp.sheaf.xif.paper.S2132D5FactorizationActual

/-!
# S2600: the last D5 bridge, from the localized twelve-cycle to the integral model

## The chain closed here

The localized model `f10'` of S2577 is a scalar multiple of the actual
five-division polynomial `S2057Psi5F` over `F' = S1720Field`.  At the
localized degree-one prime `p10` and the concrete prime `P10 W` of
`T10 = O_L[1/10]` lying over it, the arithmetic Frobenius at `P10 W`
acts on the roots of `f10'` as a twelve-cycle
(`S2600_rootPermR_cycleType`, from the localized orbit-size theorem
S2673 and the concrete `permBar` cycle type of S2667), and the same holds
for its action on the twelve actual division roots (`S2600_divisionRootEquiv_cycleType`,
via the scalar-multiple root-set transport of S2653).

The non-monic integral model `f0 = S2132Psi5Z.map (Int.castRingHom O)` has
`f0.map (algebraMap O F') = C (2^36) * S2057Psi5F` (S2577/S2003) and splits
over the actual five-division field.  Its Dedekind--Frobenius root cycle type is
the cycle type of the division-root permutation (S2653), hence is `{12}`
(`S2600_rootCycleType_f0`).

The twelve-cycle transport of S2532 (`S2532RootToRangeTransportNonmonic`, which
does not need monicity) then yields the actual twelve-cycle input
`S2440TwelveCycleInputRequired`, and S2470 turns that into the actual
pair-transitivity target `S2470Target`.

Every declaration below is kernel checked; no unproved placeholder, no
vacuous gate and no computational decision shortcut is used.
-/

noncomputable section
set_option maxHeartbeats 32000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial NumberField

namespace LeanFormal.IUT.XiFPaper.S2600D5ShortActual

open LeanFormal.IUT.XiFPaper

attribute [local instance] Ideal.Quotient.field

abbrev R10 : Type := S2537ConcreteLocalizationActual.R
abbrev T10 : Type := S2537ConcreteLocalizationActual.S
abbrev K : Type := S1720SourceArithmeticActual.S1720Field
abbrev L : Type := S2057DedekindFrobBridgeActual.S2057FiveDivisionField
abbrev O : Type := RingOfIntegers S1720SourceArithmeticActual.S1720Field

abbrev f10' : R10[X] := S2577Away10FbarActual.f10'
abbrev p10 : Ideal R10 := S2577Away10FbarActual.p10
abbrev P10 : Ideal T10 := S2663P10PrimeActual.P10 S2577Away10FbarActual.W

/-- The non-monic integral model of `psi_5` used by the range transport. -/
abbrev f0 : O[X] := S2132D5FactorizationActual.S2132Psi5Z.map (Int.castRingHom O)

local instance inst_p10_max : p10.IsMaximal := S2577Away10FbarActual.p10_max
local instance inst_P10_prime : P10.IsPrime := S2581S2543ParamsActual.P10_prime_self
local instance inst_P10_over : P10.LiesOver p10 := S2581S2543ParamsActual.P10_lies_p10_self
local instance inst_P10_max : P10.IsMaximal := S2581S2543ParamsActual.P10_isMaximal_self
local instance inst_fintype_P10 : Fintype (T10 ⧸ P10) :=
  S2665P10FintypeActual.P10_fintype S2577Away10FbarActual.W
local instance inst_decEq_P10 : DecidableEq (T10 ⧸ P10) := Classical.decEq _

/-! ## 0. Two basic facts about the localized model -/

/-- The localized model has degree twelve. -/
theorem S2600_f10'_natDegree_ne_zero : f10'.natDegree ≠ 0 := by
  rw [show f10'.natDegree = 12 from S2577Away10FbarActual.f10'_natDegree]
  norm_num

/-- The localized model is separable over `F'`. -/
theorem S2600_f10'_hsepK : (f10'.map (algebraMap R10 K)).Separable := by
  rw [show f10'.map (algebraMap R10 K) =
    Polynomial.C ((5 : K)⁻¹) * S2057DedekindFrobBridgeActual.S2057Psi5F from
    S2577Away10FbarActual.f10'_map_scalar]
  have h : (S2057DedekindFrobBridgeActual.S2057Psi5F *
      Polynomial.C ((5 : K)⁻¹)).Separable :=
    S2057DedekindFrobBridgeActual.S2057Psi5F_separable.mul_unit
      (isUnit_C.mpr (by norm_num))
  simpa [mul_comm] using h

/-! ## 1. The concrete `permBar` at `(f10', p10, P10 W)` is a twelve-cycle -/

/-- The q-Frobenius permutation of the roots of `f10' mod p10` at `P10 W`
has cycle type `{12}`: the concrete localized cycle-type computation of
S2667, restated in the local instance context of this file. -/
theorem S2600_permBar_cycleType :
    (S2540AbstractPermBarActual.permBar (f := f10') (p := p10) (P := P10)).cycleType =
      ({12} : Multiset ℕ) := by
  rw [S2548ConcreteCycleTypeActual.concrete_permBar_cycleType
    (f := f10') (p := p10) (P := P10)
    (hmonic := S2598bHsepSplitActual.S2598b_hmonic)
    (hsep := S2598bHsepSplitActual.S2598b_hsep)
    (hsplit := S2598bHsepSplitActual.S2598b_hsplit)]
  exact S2667PermBarCycleActual.factorDegrees_filter_irreducible
    S2667PermBarCycleActual.fbar10_monic
    S2577Away10FbarActual.fbar10_irreducible
    S2577Away10FbarActual.fbar10_natDegree

/-! ## 2. The arithmetic Frobenius at `P10 W` acts as a twelve-cycle on the
localized roots -/

/-- The localized Dedekind--Frobenius root permutation at any arithmetic
Frobenius at `P10 W` is conjugate to the concrete `permBar`, hence is a
twelve-cycle. -/
theorem S2600_rootPermR_cycleType (sigma : Gal(L/K)) (H : IsArithFrobAt R10 sigma P10) :
    (S2532LocalizedDefinitionsActual.rootPermR R10 K L f10'
      S2598bHsepSplitActual.S2598b_hsplit sigma).cycleType = ({12} : Multiset ℕ) := by
  have hmain := S2673LocalizedOrbitSizeActual.S2673_reductionEquiv_rootPerm
    (f := f10') (p := p10) (P := P10)
    S2598bHsepSplitActual.S2598b_hmonic S2598bHsepSplitActual.S2598b_hsep
    S2598bHsepSplitActual.S2598b_hsplit S2600_f10'_natDegree_ne_zero
    S2600_f10'_hsepK sigma H
  have h := S2132FrobCycleActual.S2132cycleType_permCongr
    (e := S2673LocalizedOrbitSizeActual.S2673_reductionEquiv f10' p10 P10
      S2598bHsepSplitActual.S2598b_hmonic S2598bHsepSplitActual.S2598b_hsep
      S2598bHsepSplitActual.S2598b_hsplit S2600_f10'_natDegree_ne_zero
      S2600_f10'_hsepK)
    (σ := S2532LocalizedDefinitionsActual.rootPermR R10 K L f10'
      S2598bHsepSplitActual.S2598b_hsplit sigma)
  rw [hmain] at h
  rw [← h, S2600_permBar_cycleType]

/-- Value form of the localized root permutation. -/
lemma S2600_rootPermR_apply_val (sigma : Gal(L/K))
    (x : (f10'.map (algebraMap R10 K)).rootSet L) :
    (S2532LocalizedDefinitionsActual.rootPermR R10 K L f10'
      S2598bHsepSplitActual.S2598b_hsplit sigma x).1 = sigma x.1 := by
  simp only [S2532LocalizedDefinitionsActual.rootPermR, MulAction.toPermHom_apply,
    MulAction.toPerm_apply, Polynomial.rootSet.coe_smul, AlgEquiv.smul_def]

/-! ## 3. Transport to the twelve actual division roots -/

/-- Relabelling the localized root permutation along the scalar multiple
`f10' = C (5⁻¹) * psi_5` gives the actual action on the twelve division
roots. -/
theorem S2600_permCongr_rootPermR (sigma : Gal(L/K)) :
    (S2653DedekindToRangeActual.S2653rootSetEquiv
      (K := K) (A := L)
      (p := S2057DedekindFrobBridgeActual.S2057Psi5F)
      (q := f10'.map (algebraMap R10 K))
      (c := (5 : K)⁻¹) (inv_ne_zero (by norm_num : (5 : K) ≠ 0))
      S2577Away10FbarActual.f10'_map_scalar).permCongr
      (S2532LocalizedDefinitionsActual.rootPermR R10 K L f10'
        S2598bHsepSplitActual.S2598b_hsplit sigma) =
      S2132FrobCycleActual.S2132DivisionRootEquiv sigma := by
  ext x
  rw [Equiv.permCongr_apply]
  change (S2532LocalizedDefinitionsActual.rootPermR R10 K L f10'
      S2598bHsepSplitActual.S2598b_hsplit sigma
      ((S2653DedekindToRangeActual.S2653rootSetEquiv
        (K := K) (A := L)
        (p := S2057DedekindFrobBridgeActual.S2057Psi5F)
        (q := f10'.map (algebraMap R10 K))
        (c := (5 : K)⁻¹) (inv_ne_zero (by norm_num : (5 : K) ≠ 0))
        S2577Away10FbarActual.f10'_map_scalar).symm x)).1 =
    ((S2132FrobCycleActual.S2132DivisionRootEquiv sigma) x).1
  rw [S2600_rootPermR_apply_val]
  rfl

/-- The cycle type of the actual action on the twelve division roots at an
arithmetic Frobenius at `P10 W` is `{12}`. -/
theorem S2600_divisionRootEquiv_cycleType (sigma : Gal(L/K))
    (H : IsArithFrobAt R10 sigma P10) :
    Equiv.Perm.cycleType (S2132FrobCycleActual.S2132DivisionRootEquiv sigma) =
      ({12} : Multiset ℕ) := by
  have h := S2132FrobCycleActual.S2132cycleType_permCongr
    (e := S2653DedekindToRangeActual.S2653rootSetEquiv
      (K := K) (A := L)
      (p := S2057DedekindFrobBridgeActual.S2057Psi5F)
      (q := f10'.map (algebraMap R10 K))
      (c := (5 : K)⁻¹) (inv_ne_zero (by norm_num : (5 : K) ≠ 0))
      S2577Away10FbarActual.f10'_map_scalar)
    (σ := S2532LocalizedDefinitionsActual.rootPermR R10 K L f10'
      S2598bHsepSplitActual.S2598b_hsplit sigma)
  rw [S2600_permCongr_rootPermR sigma] at h
  rw [h]
  exact S2600_rootPermR_cycleType sigma H

/-! ## 4. The integral model `f0` -/

/-- `f0` is a nonzero scalar multiple of the actual `psi_5` over `F'`. -/
theorem S2600_hq : f0.map (algebraMap O K) =
    Polynomial.C ((2 : K) ^ 36) * S2057DedekindFrobBridgeActual.S2057Psi5F := by
  show (S2132D5FactorizationActual.S2132Psi5Z.map (Int.castRingHom O)).map
    (algebraMap O K) = _
  rw [Polynomial.map_map]
  have hcomp : (algebraMap O K).comp (Int.castRingHom O) = Int.castRingHom K := by
    ext z
    simp
  rw [hcomp, S2577Away10FbarActual.S2003Psi5Z_map_K]

/-- `f0` splits in the actual five-division field. -/
theorem S2600_hsplit : (f0.map (algebraMap O L)).Splits := by
  have h2 : f0.map (algebraMap O L) =
      (f0.map (algebraMap O K)).map (algebraMap K L) := by
    conv_rhs => rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq O K L]
  rw [h2, S2600_hq, Polynomial.map_mul, Polynomial.map_C]
  exact Polynomial.Splits.C_mul
    (Polynomial.SplittingField.splits (f := S2057DedekindFrobBridgeActual.S2057Psi5F)) _

/-- The Dedekind--Frobenius root cycle type of the non-monic integral model
`f0` at an arithmetic Frobenius at `P10 W` is `{12}`. -/
theorem S2600_rootCycleType_f0 (sigma : Gal(L/K)) (H : IsArithFrobAt R10 sigma P10) :
    S2167DedekindFrobCycleActual.rootCycleType K L f0 S2600_hsplit sigma =
      ({12} : Multiset ℕ) := by
  letI hint : DecidableEq ((f0.map (algebraMap O K)).rootSet L) := Classical.decEq _
  have h := S2653DedekindToRangeActual.S2653permCongr_rootPerm_eq_divisionRootEquiv
    (f := f0) (hsplit := S2600_hsplit) (σ := sigma) (c := (2 : K) ^ 36)
    (by norm_num) S2600_hq
  have hperm : (S2167DedekindFrobCycleActual.rootPerm K L f0 S2600_hsplit sigma).cycleType =
      ({12} : Multiset ℕ) := by
    have h' := S2132FrobCycleActual.S2132cycleType_permCongr
      (e := S2653DedekindToRangeActual.S2653rootSetEquiv
        (K := K) (A := L) (c := (2 : K) ^ 36) (by norm_num) S2600_hq)
      (σ := S2167DedekindFrobCycleActual.rootPerm K L f0 S2600_hsplit sigma)
    rw [h] at h'
    rw [← h']
    exact S2600_divisionRootEquiv_cycleType sigma H
  simpa only [S2167DedekindFrobCycleActual.rootCycleType] using hperm

/-! ## 5. Existence of the Frobenius and the twelve-cycle input -/

/-- There is an arithmetic Frobenius at `P10 W` whose permutation of the
localized roots is a twelve-cycle. -/
theorem S2600_exists_sigma :
    ∃ sigma : Gal(L/K), IsArithFrobAt R10 sigma P10 ∧
      (S2532LocalizedDefinitionsActual.rootPermR R10 K L f10'
        S2598bHsepSplitActual.S2598b_hsplit sigma).cycleType = ({12} : Multiset ℕ) := by
  haveI hInv : Algebra.IsInvariant R10 T10 Gal(L/K) :=
    Algebra.isInvariant_of_isGalois R10 K L T10
  obtain ⟨sigma, H⟩ := IsArithFrobAt.exists_of_isInvariant (S := T10) R10 (Gal(L/K)) P10
  exact ⟨sigma, H, S2600_rootPermR_cycleType sigma H⟩

/-- **The twelve-cycle input of the actual range.** -/
theorem S2600_twelveCycleInput :
    S2440RangePairTransitiveSubagentActual.S2440TwelveCycleInputRequired := by
  obtain ⟨sigma, H, _⟩ := S2600_exists_sigma
  exact S2532PairTransitiveActual.S2532RootToRangeTransportNonmonic f0 S2600_hsplit sigma
    ⟨(2 : K) ^ 36, by norm_num, S2600_hq⟩ (S2600_rootCycleType_f0 sigma H)

/-- **The actual pair-transitivity target.** -/
theorem S2600_S2470Target : S2470PairTransitiveFinalActual.S2470Target :=
  S2470PairTransitiveFinalActual.S2470Target_of_twelveCycle S2600_twelveCycleInput

/-- The same target in the S2532 form. -/
theorem S2600_S2532Target : S2532PairTransitiveActual.S2532Target :=
  S2532PairTransitiveActual.S2532Target_of_twelveCycle S2600_twelveCycleInput

/-! ## 6. The exact statements obtained -/

#check S2600_twelveCycleInput
#check S2600_S2470Target
#check S2600_S2532Target
#check S2600_rootCycleType_f0

/-! ## 7. Axiom footprint -/

#print axioms S2600_f10'_natDegree_ne_zero
#print axioms S2600_f10'_hsepK
#print axioms S2600_permBar_cycleType
#print axioms S2600_rootPermR_cycleType
#print axioms S2600_rootPermR_apply_val
#print axioms S2600_permCongr_rootPermR
#print axioms S2600_divisionRootEquiv_cycleType
#print axioms S2600_hq
#print axioms S2600_hsplit
#print axioms S2600_rootCycleType_f0
#print axioms S2600_exists_sigma
#print axioms S2600_twelveCycleInput
#print axioms S2600_S2470Target
#print axioms S2600_S2532Target

end LeanFormal.IUT.XiFPaper.S2600D5ShortActual

end
