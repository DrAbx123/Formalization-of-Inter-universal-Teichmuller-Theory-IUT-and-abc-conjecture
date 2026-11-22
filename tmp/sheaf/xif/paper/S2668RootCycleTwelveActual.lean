import tmp.sheaf.xif.paper.S2673LocalizedOrbitSizeActual
import tmp.sheaf.xif.paper.S2667PermBarCycleActual
import tmp.sheaf.xif.paper.S2657GeneralizedRootActual
import tmp.sheaf.xif.paper.S2542PairTransitiveActual
import tmp.sheaf.xif.paper.S2581S2543ParamsActual

noncomputable section
set_option maxHeartbeats 32000000
set_option maxRecDepth 100000
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual

namespace LeanFormal.IUT.XiFPaper.S2668RootCycleTwelveActual
attribute [local instance] Ideal.Quotient.field

abbrev R10 : Type := LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.R
abbrev T10 : Type := LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.S
abbrev K : Type := LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual.S1720Field
abbrev L10 : Type := LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual.S2057FiveDivisionField
abbrev f : R10[X] := LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.f10'
abbrev p : Ideal R10 := LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.p10
abbrev P : Ideal T10 := LeanFormal.IUT.XiFPaper.S2663P10PrimeActual.P10
  LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.W

local instance hp : p.IsMaximal :=
  LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.p10_max
local instance hPprime : P.IsPrime :=
  LeanFormal.IUT.XiFPaper.S2581S2543ParamsActual.P10_prime_self
local instance hPover : P.LiesOver p :=
  LeanFormal.IUT.XiFPaper.S2581S2543ParamsActual.P10_lies_p10_self
local instance hPmax : P.IsMaximal :=
  LeanFormal.IUT.XiFPaper.S2581S2543ParamsActual.P10_isMaximal_self
local instance : Fintype (R10 ⧸ p) :=
  LeanFormal.IUT.XiFPaper.S2581S2543ParamsActual.fintype_quot_p10
local instance : DecidableEq (R10 ⧸ p) :=
  LeanFormal.IUT.XiFPaper.S2581S2543ParamsActual.decEq_quot_p10
local instance : Fintype (T10 ⧸ P) :=
  LeanFormal.IUT.XiFPaper.S2665P10FintypeActual.P10_fintype
    LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.W
local instance : DecidableEq (T10 ⧸ P) := Classical.decEq _

theorem f10'_natDegree_ne_zero : f.natDegree ≠ 0 := by
  rw [show f.natDegree = 12 from
    LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.f10'_natDegree]
  norm_num

theorem f10'_hsepK : (f.map (algebraMap R10 K)).Separable := by
  rw [show f.map (algebraMap R10 K) =
    Polynomial.C ((5 : K)⁻¹) * S2057Psi5F from
    LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.f10'_map_scalar]
  exact Polynomial.Separable.unit_mul
    (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero (by norm_num : (5:K) ≠ 0))))
    S2057Psi5F_separable

theorem exists_frobenius :
    ∃ σ : Gal(L10/K), IsArithFrobAt R10 σ P := by
  haveI hInv : Algebra.IsInvariant R10 T10 Gal(L10/K) :=
    Algebra.isInvariant_of_isGalois R10 K L10 T10
  exact IsArithFrobAt.exists_of_isInvariant (S := T10) R10 (Gal(L10/K)) P

def permBarP : Equiv.Perm ((LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual.fbar f p).rootSet
  (T10 ⧸ P)) :=
  LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual.permBar (f := f) (p := p) (P := P)

theorem permBarP_cycleType : permBarP.cycleType = ({12} : Multiset ℕ) := by
  change (LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual.permBar
    (f := f) (p := p) (P := P)).cycleType = ({12} : Multiset ℕ)
  exact LeanFormal.IUT.XiFPaper.S2667PermBarCycleActual.permBar_cycleType_twelve

theorem cycleType_rootPerm (σ : Gal(L10/K)) (H : IsArithFrobAt R10 σ P) :
    (LeanFormal.IUT.XiFPaper.S2532LocalizedDefinitionsActual.rootPermR
      R10 K L10 f
      LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hsplit σ).cycleType =
      ({12} : Multiset ℕ) := by
  classical
  have hconj := LeanFormal.IUT.XiFPaper.S2673LocalizedOrbitSizeActual.S2673_reductionEquiv_rootPerm
    (f := f) (p := p) (P := P)
    LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hmonic
    LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hsep
    LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hsplit
    f10'_natDegree_ne_zero f10'_hsepK σ H
  have hcyc := congrArg Equiv.Perm.cycleType hconj
  rw [LeanFormal.IUT.XiFPaper.S2132FrobCycleActual.S2132cycleType_permCongr] at hcyc
  rw [hcyc]
  exact permBarP_cycleType

theorem divisionRootCycleTwelve (σ : Gal(L10/K)) (H : IsArithFrobAt R10 σ P) :
    Equiv.Perm.cycleType
      (LeanFormal.IUT.XiFPaper.S2132FrobCycleActual.S2132DivisionRootEquiv σ) =
      ({12} : Multiset ℕ) := by
  have hsplitK : ((f.map (algebraMap R10 K)).map (algebraMap K L10)).Splits := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq R10 K L10]
    exact LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hsplit
  have hq : f.map (algebraMap R10 K) =
      Polynomial.C ((5 : K)⁻¹) * S2057Psi5F :=
    LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.f10'_map_scalar
  have hc : (5 : K)⁻¹ ≠ 0 :=
    inv_ne_zero (by norm_num : (5 : K) ≠ 0)
  have h := LeanFormal.IUT.XiFPaper.S2657GeneralizedRootActual.S2657CycleType_eq_divisionRootEquiv
    (f := f.map (algebraMap R10 K)) hsplitK σ hc hq
  have hperm :
      LeanFormal.IUT.XiFPaper.S2532LocalizedDefinitionsActual.rootPermR
        R10 K L10 f
        LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hsplit σ =
        LeanFormal.IUT.XiFPaper.S2657GeneralizedRootActual.S2657RootPerm
          (f.map (algebraMap R10 K)) hsplitK σ := rfl
  rw [← h, ← hperm]
  exact cycleType_rootPerm σ H

theorem divisionRootCycleTwelveRequired :
    LeanFormal.IUT.XiFPaper.S2542PairTransitiveActual.S2542DivisionRootCycleTwelveRequired := by
  obtain ⟨σ, H⟩ := exists_frobenius
  exact ⟨σ, divisionRootCycleTwelve σ H⟩

theorem twelveCycleInput :
    LeanFormal.IUT.XiFPaper.S2440RangePairTransitiveSubagentActual.S2440TwelveCycleInputRequired :=
  LeanFormal.IUT.XiFPaper.S2542PairTransitiveActual.S2542DivisionRootCycleTwelve_iff_twelveCycleInput.mp
    divisionRootCycleTwelveRequired

#check twelveCycleInput

#check cycleType_rootPerm
#check exists_frobenius

end LeanFormal.IUT.XiFPaper.S2668RootCycleTwelveActual
end
