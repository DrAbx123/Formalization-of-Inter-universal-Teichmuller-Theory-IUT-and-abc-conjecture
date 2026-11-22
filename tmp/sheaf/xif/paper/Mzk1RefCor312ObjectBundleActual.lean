/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import tmp.sheaf.xif.paper.RefLANACor312ProcessionActual
import tmp.sheaf.xif.paper.RefLANAPacketPresentationActual
import tmp.sheaf.xif.paper.RefLANAHodgeLabelsActual

/-! A516/A517: 3.12-route combinatorial/packet object bundle built from the
green RefLANA Cor312 files: the procession of capsules (procLabels), a concrete
direct-sum-of-fields packet presentation with its integral/product/hull regions,
and the Hodge-theater label counts (FlStar/FlSemi/absFl). No new axioms. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1RefCor312ObjectBundleActual

open Iut
open Iut.HodgeTheater

/-! ## 1. The procession labels -/

/-- The capsule labels `S_{j+1} = {0,...,j}` have cardinality j+1. -/
theorem procLabels_card (j : Nat) : (procLabels j).card = j + 1 := by
  rw [Iut.card_procLabels]

/-- Procession label monotonicity. -/
theorem procLabels_subset {i j : Nat} (h : i <= j) : procLabels i <= procLabels j := by
  rw [Iut.procLabels_mono h]

/-! ## 2. A concrete p-adic direct-sum packet presentation -/

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- The concrete 2-component p-adic packet presentation (Q_11 summands with
integral structure Z_11). This is the instantiated interface of IUT III,
Proposition 3.1 / Remark 3.9.5. -/
def padicPacketPresentation : Iut.DirectSumPresentation (Fin 2) where
  Summand := fun _ => ℚ_[11]
  ring_summand := fun _ => inferInstance
  topology_summand := fun _ => inferInstance
  integral := fun _ => (ℤ_[11] : Set ℚ_[11])

theorem padicPacketPresentation_constructed :
    (padicPacketPresentation : Iut.DirectSumPresentation (Fin 2)).integral =
      fun _ => (ℤ_[11] : Set ℚ_[11]) := rfl

/-- The integral region of the concrete presentation. -/
def padicIntegralRegion : Set padicPacketPresentation.Total :=
  padicPacketPresentation.integralRegion

theorem padicIntegralRegion_eq :
    padicIntegralRegion =
      {x | forall c, x c ∈ (ℤ_[11] : Set ℚ_[11])} := rfl

theorem padicIntegralRegion_isProductRegion :
    padicPacketPresentation.IsProductRegion padicIntegralRegion :=
  padicPacketPresentation.isProductRegion_integralRegion

theorem padicIntegralRegion_isHullRegion :
    padicPacketPresentation.IsHullRegion padicIntegralRegion :=
  padicPacketPresentation.isHullRegion_integralRegion

/-- The unit scaled integral region is the integral region. -/
theorem padicScaledIntegral_one :
    padicPacketPresentation.scaledIntegral (fun _ => 1) = padicIntegralRegion := by
  rw [Iut.DirectSumPresentation.scaledIntegral_one]

/-- The integral region is a scale of itself, i.e. a hull region (Remark 3.9.5). -/
theorem padicIntegralRegion_hull :
    exists a : padicPacketPresentation.Total,
      (forall c, IsUnit (a c)) ∧
        padicIntegralRegion = padicPacketPresentation.scaledIntegral a := by
  refine ⟨fun _ => 1, fun _ => isUnit_one, ?_⟩
  rw [padicScaledIntegral_one]

/-! ## 3. Hodge-theater label counts -/

theorem flStar_card_eq_half_pred (ell : Nat) [OddPrime ell] :
    Nat.card (FlStar ell) = (ell - 1) / 2 := by
  rw [Iut.HodgeTheater.card_flStar]
  rfl

theorem flSemi_card (ell : Nat) [OddPrime ell] :
    Nat.card (FlSemi ell) = 2 * ell := Iut.HodgeTheater.card_flSemi ell

theorem absFl_card (ell : Nat) [OddPrime ell] :
    Nat.card (AbsFl ell) = ellStar ell + 1 := by
  rw [Iut.HodgeTheater.card_absFl]
  rfl

/-! ## 4. The combined 3.12 combinatorial object -/

/-- The combinatorial/packet data of one Cor 3.12 procession level. -/
structure Cor312CombinatorialObject (ell j : Nat) [OddPrime ell] where
  capsuleCard : Nat
  capsuleCard_eq : capsuleCard = j + 1
  flStarCard : Nat
  flStarCard_eq : flStarCard = Nat.card (FlStar ell)
  flSemiCard : Nat
  flSemiCard_eq : flSemiCard = Nat.card (FlSemi ell)
  packetIntegralRegion : Set padicPacketPresentation.Total
  packetIntegralRegion_eq : packetIntegralRegion = padicIntegralRegion

noncomputable def cor312CombinatorialObject (ell j : Nat) [OddPrime ell] :
    Cor312CombinatorialObject ell j where
  capsuleCard := (procLabels j).card
  capsuleCard_eq := Iut.card_procLabels j
  flStarCard := Nat.card (FlStar ell)
  flStarCard_eq := rfl
  flSemiCard := Nat.card (FlSemi ell)
  flSemiCard_eq := rfl
  packetIntegralRegion := padicIntegralRegion
  packetIntegralRegion_eq := rfl

theorem cor312CombinatorialObject_constructed (ell j : Nat) [OddPrime ell] :
    (cor312CombinatorialObject ell j).capsuleCard = j + 1 ∧
    (cor312CombinatorialObject ell j).flStarCard = Nat.card (FlStar ell) := by
  refine ⟨Iut.card_procLabels j, rfl⟩

end LeanFormal.IUT.XiFPaper.Mzk1RefCor312ObjectBundleActual