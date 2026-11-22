import tmp.sheaf.xif.PaperQPilotObject
import tmp.sheaf.xif.PaperQPilotLogVolume

/-! # S631: source q identification—exact minimal equality

The concrete scalar is
  sourceQPilotSignedLog S = - sum_{b : S.badPlaces} |log (qParameter b)|,
while the C3 scalar is
  paperQPilotLogVolume C3 = localSignedLog C3.q = Real.log ||C3.q.q||.
The requested source q identification is exactly the equality of these two
actual formulas.  The donor field C3.q is an arbitrary FinitePlaceQCandidate;
neither C3 nor QPilotLineActual carries a relation between that q and the bad
qParameter family.  Hence the equality is recorded exactly, not fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.Theorem311Source.S631SourceQIdentificationActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8Closure.SourcePilotRegion

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- Expanded source scalar: negative sum of bad q absolute logs. -/
theorem sourceQPilotSignedLog_unfold
    (S : SourceDefinition31Data l) :
    sourceQPilotSignedLog S =
      (letI := S.bad_finite;
        -(∑ b : S.badPlaces, |Real.log (S.reduction.qParameter b)|)) := by
  rfl

/-- Expanded C3 scalar. -/
theorem paperQPilotLogVolume_C3_unfold
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    paperQPilotLogVolume C3 = Real.log ‖C3.q.q‖ := by
  rfl

/-- Exact minimal source equality. -/
def SourceQIdentification
    (S : SourceDefinition31Data l)
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop :=
  sourceQPilotSignedLog S = paperQPilotLogVolume C3

/-- Formula form of the same equality. -/
def SourceQIdentificationFormula
    (S : SourceDefinition31Data l)
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop :=
  (letI := S.bad_finite;
    -(∑ b : S.badPlaces, |Real.log (S.reduction.qParameter b)|)) =
      Real.log ‖C3.q.q‖

theorem sourceQIdentification_iff_formula
    (S : SourceDefinition31Data l)
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    SourceQIdentification S C3 ↔ SourceQIdentificationFormula S C3 := by
  unfold SourceQIdentification SourceQIdentificationFormula
  rw [sourceQPilotSignedLog_unfold, paperQPilotLogVolume_C3_unfold]

theorem sourceQIdentification_of_formula
    (S : SourceDefinition31Data l)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (h : SourceQIdentificationFormula S C3) :
    SourceQIdentification S C3 :=
  (sourceQIdentification_iff_formula S C3).mpr h

/-- Exact missing source link datum. -/
structure SourceQEqualityWitness
    (S : SourceDefinition31Data l)
    (C3 : SourcePilotRegionData (l := l) (V := V) I) where
  formula : SourceQIdentificationFormula S C3
  source_q_link : Prop

def SourceQEqualityWitnessRequired
    (S : SourceDefinition31Data l)
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop :=
  Nonempty (SourceQEqualityWitness S C3)

end LeanFormal.IUT.Theorem311Source.S631SourceQIdentificationActual
end
