/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ClassicalABCBridgeActual
import tmp.sheaf.xif.paper.Mzk1E1DictionaryActual
import tmp.sheaf.xif.paper.Mzk1E4DictionaryActual
import tmp.sheaf.xif.paper.Mzk1StepVVolumeUpperActual
import tmp.sheaf.xif.paper.Mzk1E1OrderActual
import Mathlib.Tactic

/-! # A930/A933: our-framework ABC assembly — E1-E4 as explicit interface fields

**Status: MODEL** (conditional interface; NOT a theorem of ABC and not unconditional).

CONDITIONAL STATEMENT: this file does NOT prove ABC.  The theorem below consumes ONLY the
E3 field (ABC-level input); E1, E2, E4 are UPSTREAM obligations of the route, not derivation
steps in this file.  Fields:
* E1: `Mzk1E1DictionaryActual.E1Dictionary V_norm V_hull` (= `V_norm = V_hull`);
* E2: real volume-upper statement `V <= ((l+5)/4)*logdf + C0`, with
  `logdf = Mzk1StepVVolumeUpperActual.logdf logd logf = logd + logf`;
* E3: `ClassicalABCNatShape` (proof field; equivalent to ABC via A875);
* E4: `Mzk1E4DictionaryActual.E4Dictionary R P sF A VolShell`, whose green consumer
  `e4_inequality` gives `(sF-1)*A <= VolShell` (consumed below).

试金石 defer: 本阶段不主张不等式；试金石仅在其数据被 A3/B1/C3 定理化时适用，
届时在相应主张中回答（本轮：不适用/暂缓）。

No direct lana imports; the import closure is lana-transitive via existing green modules
(`Iut.Foundations.Frobenioid`), so this file is NOT lana-free citable. No sorry/axiom. -/

noncomputable section

open LeanFormal.IUT.XiFPaper.Mzk1ClassicalABCBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1E1DictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1E4DictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1StepVVolumeUpperActual
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.Mzk1OurFrameworkABCActual

/-- E2: real volume-upper statement (logdf from the green `logdf logd logf = logd + logf`). -/
def E2VolumeUpper (V logd logf C0 l : ℝ) : Prop :=
  V ≤ ((l + 5) / 4) * Mzk1StepVVolumeUpperActual.logdf logd logf + C0

structure OurFrameworkAssumptions (α : Type) where
  V_norm : ℝ
  V_hull : ℝ
  E1_normalization : E1Dictionary V_norm V_hull
  E1_qSide : ℝ
  E1_allocation : Mzk1E1OrderActual.E1AllocationForm V_norm V_hull E1_qSide
  E2_V : ℝ
  E2_logd : ℝ
  E2_logf : ℝ
  E2_C0 : ℝ
  E2_l : ℝ
  E2_volume_upper : E2VolumeUpper E2_V E2_logd E2_logf E2_C0 E2_l
  E4_R : Set α
  E4_P : Set α
  E4_sF : ℝ
  E4_A : ℝ
  E4_VolShell : ℝ
  E4_containment : RegionLe E4_R E4_P
  E4_dictionary : E4Dictionary E4_R E4_P E4_sF E4_A E4_VolShell
  E3_interface : ClassicalABCNatShape

/-- **Conditional assembly**: under the explicit assumptions (in particular E3),
`ABCConjecture` follows from the proved equivalence
`ClassicalABCNatShape <-> ABCConjecture`.  Only E3 is consumed here; NOT a proof of ABC. -/
theorem ourFramework_ABCConjecture {α : Type} (A : OurFrameworkAssumptions α) :
    ABCConjecture := by
  exact (classicalABCNatShape_iff_ABCConjecture).mp A.E3_interface

/-- E1 consumption: the normalization identity. -/
theorem ourFramework_E1 {α : Type} (A : OurFrameworkAssumptions α) :
    A.V_norm = A.V_hull := A.E1_normalization

/-- E1 allocation form (A936 correct interface): `V_norm = V_hull + qSide`. -/
theorem ourFramework_E1_allocation {α : Type} (A : OurFrameworkAssumptions α) :
    A.V_norm = A.V_hull + A.E1_qSide := by
  exact A.E1_allocation

/-- Paper E1 form recovered when the q-side contribution vanishes. -/
theorem ourFramework_E1_of_qSide_zero {α : Type} (A : OurFrameworkAssumptions α)
    (hq : A.E1_qSide = 0) : A.V_norm = A.V_hull := by
  have h : A.V_norm = A.V_hull + A.E1_qSide := A.E1_allocation
  rw [hq, add_zero] at h
  exact h

/-- E4 consumption: `(sF-1)*A <= VolShell` from the E4 dictionary (green consumer). -/
theorem ourFramework_E4 {α : Type} (A : OurFrameworkAssumptions α) :
    (A.E4_sF - 1) * A.E4_A ≤ A.E4_VolShell :=
  e4_inequality A.E4_dictionary A.E4_containment

/-- E2 is the real volume-upper statement (not an empty Prop). -/
theorem ourFramework_E2 {α : Type} (A : OurFrameworkAssumptions α) :
    A.E2_V ≤ ((A.E2_l + 5) / 4) * Mzk1StepVVolumeUpperActual.logdf A.E2_logd A.E2_logf + A.E2_C0 :=
  A.E2_volume_upper

def assumptionInterfaceRows : List (String × String × String) :=
  [ ("E1 normalization", "E1Dictionary V_norm V_hull (Mzk1E1DictionaryActual)", "DEF") ,
    ("E2 volume upper", "V <= ((l+5)/4)*logdf + C0, logdf=logd+logf (Mzk1StepVVolumeUpperActual)", "DEF") ,
    ("E3 interface", "ClassicalABCNatShape (proof field; equivalent to ABC)", "PROOF FIELD (ABC-equivalent)") ,
    ("E4 dictionary", "E4Dictionary R P sF A VolShell (Mzk1E4DictionaryActual)", "DEF + GAP") ,
    ("ourFramework_ABCConjecture", "conditional: ONLY E3 consumed", "CONDITIONAL") ,
    ("E1 allocation form", "V_norm = V_hull + qSide (A936 correct interface)", "PROVED") ,
    ("Status", "MODEL (conditional interface)", "MODEL") ,
    ("lana-free closure", "Frobenioid olean+source exist; green paths transitively import it", "NOT CITABLE (lana-transitive)") ]

theorem assumptionInterfaceRows_length : assumptionInterfaceRows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1OurFrameworkABCActual
