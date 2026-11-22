/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0LPaperInstanceActual
import tmp.sheaf.xif.paper.Mzk1P0NativeReadoutActual
import tmp.sheaf.xif.paper.Mzk1P0NativeComparisonActual
import Mathlib.Tactic
/-! # P0.5: theta alignment (L actual readout vs native theta readout) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0ThetaAlignmentActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual
universe ua upi umon ui
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable {I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)}
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
/-- Exact theta alignment: L theta readout equals native theta readout. -/
def ThetaAlignment : Prop := thetaReadActual I place = nativeThetaReadout T b
/-- Exact Haar normalization factor of the L/native theta readout gap. -/
noncomputable def thetaNormalizationFactor : Real :=
  Real.exp (thetaReadActual I place - nativeThetaReadout T b)
theorem thetaReadActual_eq_native_add_log_factor :
    thetaReadActual I place =
      nativeThetaReadout T b + Real.log (thetaNormalizationFactor T b (I := I) place) := by
  unfold thetaNormalizationFactor
  rw [Real.log_exp]
  ring
/-- Conditional transfer: explicit q and theta alignments plus native comparison give LPaperInstance. -/
theorem LPaperInstance_of_nativeComparison_of_alignments
    (hq : qReadActual I place = nativeQReadout T b)
    (hθ : ThetaAlignment T b (I := I) place)
    (h : LeanFormal.IUT.XiFPaper.Mzk1P0NativeComparisonActual.NativeComparison T b) : LPaperInstance I place := by
  unfold LPaperInstance
  change qReadActual I place ≤ thetaReadActual I place
  unfold ThetaAlignment at hθ
  rw [hq, hθ]
  exact h
/-- Exact missing L theta source arrow, from stepxi's structure. -/
def ThetaSourceArrowMissing : Prop := LQThetaSourceArrowMissing I place
def rows : List String :=
  ["theta alignment: thetaReadActual = nativeThetaReadout (explicit Prop)",
   "factor: exp(Ltheta - nativeTheta), expected Haar normalization not identified",
   "L theta source arrow: q_mem_thetaRegion + normalization_eq (stepxi)",
   "transfer: hq+hθ+NativeComparison => LPaperInstance"]
theorem rows_length : rows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P0ThetaAlignmentActual
end