import tmp.sheaf.xif.paper.S1009HQHC3Actual

/-! # S1026: exact form of the S1009 source-q identification

S1009SourceQIdentification unfolds to the actual scalar equality
  -sum_b |log qParameter b| = log ||C3.q.q||.
This file proves the exact equivalence and the conditional actual theorem.
The concrete source data currently provide no relation between qParameter and
C3.q, so the formula equality is the exact minimal input.  No fake proof. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S1026SourceQIdentificationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1009HQHC3Actual
open MeasureTheory

universe uX uLabel uC3 uD3 uM uP ua uv upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (P : PaperSignedHull X label)
variable (C1 : SourceInputBinding I)
variable (C2 : SourceLogKummerData I C1)
variable (C3 : SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I)

/-- Exact formula form of the S1009 source-q identification. -/
def S1026SourceQExactFormula (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (C3 : SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I) : Prop :=
  letI : Fintype I.initial.badPlaces := I.initial.bad_finite;
  -(∑ b : I.initial.badPlaces,
      |Real.log (I.initial.reduction.qParameter b)|) =
    Real.log ‖C3.q.q‖

/-- S1009's identification is exactly the formula equality. -/
theorem s1026SourceQIdentification_iff_formula :
    S1009SourceQIdentification (l := l) I C3 ↔
      S1026SourceQExactFormula I C3 := by
  letI : Fintype I.initial.badPlaces := I.initial.bad_finite
  unfold S1009SourceQIdentification S1026SourceQExactFormula
    sourceQPilotSignedLog sourceBadQAbsLog localSignedLog
  rfl

/-- Conditional actual theorem: the exact formula gives the S1009 identification. -/
theorem s1026SourceQIdentification_of_formula
    (h : S1026SourceQExactFormula I C3) :
    S1009SourceQIdentification (l := l) I C3 :=
  (s1026SourceQIdentification_iff_formula (l := l) I C3).mpr h

/-- Exact minimal input for S1009. -/
def S1026SourceQExactMinimum
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (C3 : SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I) : Prop :=
  S1026SourceQExactFormula I C3

theorem s1026SourceQIdentification_iff_exactMinimum :
    S1009SourceQIdentification (l := l) I C3 ↔
      S1026SourceQExactMinimum I C3 :=
  s1026SourceQIdentification_iff_formula (l := l) I C3

end LeanFormal.IUT.XiFPaper.S1026SourceQIdentificationActual

end
