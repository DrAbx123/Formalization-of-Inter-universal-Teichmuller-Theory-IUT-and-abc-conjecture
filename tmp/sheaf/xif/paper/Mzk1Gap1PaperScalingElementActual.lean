/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Gap1ScalingLawTargetActual
import tmp.sheaf.xif.paper.Mzk1LanaBridgeAuditActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-!
# A657 GAP1 via the CORRECT paper scaling element (mainline)

The A656 reduction shows Gap 1 must come from an exact scaling law of the comparison
region.  The paper's scaling element is the **q-pilot**, whose data is bad-supported
and whose `|log q|` is comparable to the height `log c` (the q-pilot varies with the
triple).  This file formalizes the matching condition and proves:

* `ScalingElementMatches`: the scaling element is bad-supported and its log-size
  dominates `log c` (the paper q-pilot property, as a named condition);
* `gap1_of_matchingScalingElement`: if the region's exact scaling law uses `exp(size)`
  and unit/const are nonnegative, then Gap 1 HOLDS (theorem);
* `missingLemmas`: the two exact lemmas NOT available from current green data — the
  q-pilot bad-support/size-vs-height arithmetic, and its carrier correspondence.

Nothing canonical is changed; missing lemmas are recorded as audit rows (not proved).
ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Gap1PaperScalingElementActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap1ScalingLawTargetActual
open Mzk1LanaBridgeAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- The paper scaling-element condition: `q` is bad-supported (variation only at bad
  places) and its log-size dominates the height `log c`. -/
structure ScalingElementMatches
    (q : Nat → Nat → Nat → S1902Carrier T)
    (qLogSize : Nat → Nat → Nat → ℝ)
    (BadSupported : (Nat → Nat → Nat → S1902Carrier T) → Prop) : Prop where
  bad_supported : BadSupported q
  size_ge_height : ∀ a b c : Nat, IsABCTriple a b c →
    Real.log (c : ℝ) ≤ qLogSize a b c

/-- **Gap 1 from a matching scaling element**: if the exact scaling law of the region
  uses `exp (qLogSize)` as ratio and unit/const are nonnegative, then Gap 1 holds. -/
theorem gap1_of_matchingScalingElement
    (q : Nat → Nat → Nat → S1902Carrier T)
    (qLogSize : Nat → Nat → Nat → ℝ)
    (BadSupported : (Nat → Nat → Nat → S1902Carrier T) → Prop)
    (hmatch : ScalingElementMatches T q qLogSize BadSupported)
    (const ε : ℝ) (hε : 0 < ε)
    (hvol : PaperRegionScalingLaw T q (fun a b c => Real.exp (qLogSize a b c)) const)
    (hunit : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal)
    (hconst : 0 ≤ const) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + ε) *
          (s1902LogVolume T (paperComparisonRegion T q a b c)).toReal := by
  refine gap1_of_scalingLaw_and_arith T q (fun a b c => Real.exp (qLogSize a b c))
    const ε hε hvol ?_
  intro a b c habc
  have hsize := hmatch.size_ge_height a b c habc
  have hlogc : 0 < Real.log (c : ℝ) := by
    have hc2 : 2 ≤ c := by
      have hstruct : 0 < a ∧ 0 < b ∧ a + b = c ∧ Nat.Coprime a b := habc
      rcases hstruct with ⟨ha, hb, hsum, _⟩
      omega
    have hc2R : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc2
    have : (1 : ℝ) < (c : ℝ) := by linarith
    exact Real.log_pos this
  have hpos : 0 < qLogSize a b c := lt_of_lt_of_le hlogc hsize
  have hlogratio : Real.log (Real.exp (qLogSize a b c)) = qLogSize a b c :=
    Real.log_exp _
  have hX : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal +
      Real.log (Real.exp (qLogSize a b c)) + const := by
    rw [hlogratio]; linarith
  have hle1 : (1 : ℝ) ≤ 1 + ε := by linarith
  calc Real.log (c : ℝ) ≤ qLogSize a b c := hsize
    _ = Real.log (Real.exp (qLogSize a b c)) := hlogratio.symm
    _ = 1 * Real.log (Real.exp (qLogSize a b c)) := by ring
    _ ≤ (1 + ε) * ((s1902LogVolume T (s1902UnitRegion T)).toReal +
          Real.log (Real.exp (qLogSize a b c)) + const) := by
        exact mul_le_mul hle1 (by linarith) (by rw [hlogratio]; exact hpos.le) (by linarith)

/-- Exact missing lemmas for closing Gap 1 through the paper q-pilot (audit rows;
  none of them is proved in the current green data). -/
def missingLemmas : List (String × String) :=
  [ ("q-pilot bad-support arithmetic",
      "q-pilot (per triple) is supported at bad places; |log q| computed from bad data"),
    ("q-pilot size vs height",
      "-qPilotLogVolume P >= log c (currently only qPilotLogVolume <= 0 is green)"),
    ("q-pilot carrier correspondence",
      "paper q-pilot object P maps to qPilotInThetaCarrier T / (lift of) S1902Carrier"),
    ("exact scaling law via q",
      "(s1902LogVolume (q^{-1}•unit ∪ point)).toReal = unit + log(size q) + const") ]

theorem missingLemmas_length : missingLemmas.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Gap1PaperScalingElementActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap1PaperScalingElementActual.gap1_of_matchingScalingElement