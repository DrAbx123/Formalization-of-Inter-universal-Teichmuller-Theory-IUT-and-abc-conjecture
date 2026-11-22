/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Gap2ArithmeticReductionActual
import tmp.sheaf.xif.paper.Mzk1BadPartActual
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

/-! # A690 hull: `BadSumWeightBound` with the explicit `natRadical` weight

The remaining named input of the final boundary is the corrected-region Gap 2
shape, equivalent (`correctedGap2_iff_arith`) to the pure arithmetic
`BadSumWeightBound`.  Mainline's statement uses `arithmeticWeight`; the exact
dictionary `arithmeticWeight (abcRationalPoint a c) = Real.log (natRadical (a*b*c))`
(`arithmeticWeight_abcRationalPoint`, green `RationalPrimeSupport`) makes the
radical form explicit:

  `Σ_b e_b d_b log p_b ≤ (1+ε) * log (natRadical (a*b*c)) + D'`.

We prove the equivalence of the two formulations and the corrected-Gap2 form
against the radical weight.  No canonical object changed; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1BadSumRadicalActual

open scoped Pointwise ENNReal BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Radical-weight form of the pure arithmetic inequality. -/
def NatRadicalWeightBound
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, ∀ aN bN cN : Nat, IsABCTriple aN bN cN →
    (∑ bBad : Bad (nativePlaceSelection T),
      (eN aN bN cN bBad : ℝ) *
        ((Module.finrank ℚ_[(qVFamTensorP T bBad)] (rootNormedExtension T bBad) : ℝ) *
          Real.log ((qVFamTensorP T bBad : ℕ) : ℝ))) ≤
      (1 + ε) * Real.log (natRadical (aN * bN * cN) : ℝ) + D

/-- The mainline `BadSumWeightBound` is exactly the `natRadical` form. -/
theorem badSumWeightBound_iff_natRadical
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat) :
    BadSumWeightBound T eN ↔ NatRadicalWeightBound T eN := by
  constructor
  · intro h ε hε
    obtain ⟨D, hD⟩ := h ε hε
    refine ⟨D, ?_⟩
    intro aN bN cN habc
    have hw := arithmeticWeight_abcRationalPoint habc
    have hD' := hD aN bN cN habc
    rw [hw] at hD'
    exact hD'
  · intro h ε hε
    obtain ⟨D, hD⟩ := h ε hε
    refine ⟨D, ?_⟩
    intro aN bN cN habc
    have hw := arithmeticWeight_abcRationalPoint habc
    have hD' := hD aN bN cN habc
    rw [← hw] at hD'
    exact hD'

/-- Corrected-region Gap 2, expressed with the explicit radical weight. -/
theorem correctedGap2_iff_natRadical
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (hhull : 0 ≤ (s1902LogVolume T (s1902Hull T)).toReal) :
    CorrectedGap2Shape T point eN ↔ NatRadicalWeightBound T eN := by
  rw [correctedGap2_iff_arith T point eN hc0 hcT hhull]
  exact badSumWeightBound_iff_natRadical T eN

def badSumRadicalRows : List (String × String × String) :=
  [ ("radical dictionary", "arithmeticWeight_abcRationalPoint", "PROVED (green RationalPrimeSupport)"),
    ("BadSumWeightBound ⇔ radical form", "badSumWeightBound_iff_natRadical", "PROVED-CHAIN"),
    ("corrected Gap2 ⇔ radical form", "correctedGap2_iff_natRadical", "PROVED-CHAIN (via mainline correctedGap2_iff_arith)"),
    ("remaining named input", "NatRadicalWeightBound", "NAMED (pure arithmetic)"),
    ("tightness / converse (ABC ⇒ Gap2)", "NatRadicalWeightBound direction", "NOT-PROVED / NOT CLAIMED"),
    ("V2 certificate link", "finalBoundaryCertificateV2 consumes correctedGap2 shape", "PROVED-CHAIN"),
    ("scope", "ABC gate NOT passed; no canonical change", "INTEGRITY") ]

theorem badSumRadicalRows_length : badSumRadicalRows.length = 7 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1BadSumRadicalActual.badSumWeightBound_iff_natRadical
#print axioms LeanFormal.IUT.XiFPaper.Mzk1BadSumRadicalActual.correctedGap2_iff_natRadical

end LeanFormal.IUT.XiFPaper.Mzk1BadSumRadicalActual

end