/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PaperComparisonRegionScalingActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-!
# A699 paper q-pilot route: second faithful model (mainline)

The current model's gap uses the bad-support sum of `N = a+b+c+1`; the paper's actual
object is the q-pilot with signed log-size `s`.  This file formalizes the q-pilot route
as an explicit data structure and shows:

* `gap1_of_qPilotRoute`: nonnegative signed size + height bound (`height <= s`) +
  region log law (`logVol region = unit + s`) + unit >= 0 imply Gap 1;
* `qPilotRadicalBound`: the remaining named input in q-pilot form
  (`s <= (1+ε) weight + D`);
* `qPilotRadicalBound_implies_ABC`: it implies ABC;
* scope: the q-pilot route has the SAME strength boundary as the N-scaling route; it
  is a more faithful shape of the boundary, not a removal of the difficulty.

Does not import any red q-pilot draft; no canonical change; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1QPilotRouteActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Explicit q-pilot scale data: signed size `s`, height bound and region log law. -/
structure QPilotScaleData
    (point : Nat → Nat → Nat → S1902Carrier T) where
  /-- q-pilot signed log-size `s a b c` (the paper's `|log q|` quantity). -/
  s : Nat → Nat → Nat → ℝ
  h_nonneg : ∀ a b c : Nat, 0 ≤ s a b c
  height_bound : ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤ s a b c
  region_logLaw : ∀ a b c : Nat,
    (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal =
      (s1902LogVolume T (s1902UnitRegion T)).toReal + s a b c
  unit_nonneg : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal

/-- **Gap 1 from the q-pilot route** (theorem under the explicit q-pilot data). -/
theorem gap1_of_qPilotRoute
    (point : Nat → Nat → Nat → S1902Carrier T)
    (D : QPilotScaleData T point) (ε : ℝ) (hε : 0 < ε) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + ε) * (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal := by
  intro a b c habc
  have hheight := D.height_bound a b c habc
  have hvol := D.region_logLaw a b c
  have hnonneg : 0 ≤ (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal := by
    rw [hvol]; linarith [D.unit_nonneg, D.h_nonneg a b c]
  have hle1 : (1 : ℝ) ≤ 1 + ε := by linarith
  calc Height.logHeight₁ (abcRationalPoint a c) ≤ D.s a b c := hheight
    _ ≤ (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal := by
        rw [hvol]; linarith [D.unit_nonneg]
    _ ≤ (1 + ε) * (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal := by
        calc (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal
            = 1 * (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal := by ring
          _ ≤ (1 + ε) * (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal := by
              exact mul_le_mul_of_nonneg_right hle1 hnonneg

/-- The remaining named input in q-pilot form. -/
def qPilotRadicalBound (point : Nat → Nat → Nat → S1902Carrier T)
    (D : QPilotScaleData T point) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ D0 : ℝ, ∀ a b c : Nat, IsABCTriple a b c →
    D.s a b c ≤ (1 + ε) * arithmeticWeight (abcRationalPoint a c) + D0

/-- The q-pilot radical bound implies ABC (same strength as the N-scaling route). -/
theorem qPilotRadicalBound_implies_ABC
    (point : Nat → Nat → Nat → S1902Carrier T)
    (D : QPilotScaleData T point)
    (hbound : qPilotRadicalBound T point D) : ABCConjecture := by
  refine abcConjecture_iff_abcArithmeticWeightHeightBound.mpr ?_
  intro ε hε
  obtain ⟨D0, hD0⟩ := hbound ε hε
  refine ⟨D0, ?_⟩
  intro a b c habc
  have hh := D.height_bound a b c habc
  have hD' := hD0 a b c habc
  linarith

/-- Scope rows of the q-pilot route. -/
def qPilotRows : List (String × String) :=
  [ ("q-pilot scale data", "explicit structure (s, height bound, log law, unit >= 0)"),
    ("Gap 1 via q-pilot route", "PROVED (gap1_of_qPilotRoute)"),
    ("remaining named input", "qPilotRadicalBound: s <= (1+ε) weight + D0"),
    ("named input => ABC", "PROVED (qPilotRadicalBound_implies_ABC)"),
    ("scope", "same ABC strength as N-scaling; more faithful shape; ABC gate NOT passed") ]

theorem qPilotRows_length : qPilotRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1QPilotRouteActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1QPilotRouteActual.gap1_of_qPilotRoute
#print axioms LeanFormal.IUT.XiFPaper.Mzk1QPilotRouteActual.qPilotRadicalBound_implies_ABC
#print axioms LeanFormal.IUT.XiFPaper.Mzk1QPilotRouteActual.qPilotRows_length