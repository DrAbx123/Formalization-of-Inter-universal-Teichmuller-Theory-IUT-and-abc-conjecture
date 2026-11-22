import tmp.sheaf.xif.paper.S2556CorrectedPaperC9OutputActual
import tmp.sheaf.xif.paper.S2558C9SourceObjectsAuditActual

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6ChainA
open LeanFormal.IUT.N8Closure.P6AdmRedesign
open LeanFormal.IUT.XiFPaper.S2556CorrectedPaperC9OutputActual
open LeanFormal.IUT.XiFPaper.S2558C9SourceObjectsAuditActual

namespace LeanFormal.IUT.XiFPaper.S2559CorrectedC9IntegrationActual

universe u
variable {l : PrimeGeFive} {X : N8NativeInput l}
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Corrected C9 output plus corrected source L_q donor. -/
structure S2559CorrectedC9 where
  chainA : P6ChainAData X
  source : S2558RelaxedSourceGlobalLqDonor (mu := mu)

noncomputable def S2559CorrectedC9.toOutput
    (O : S2559CorrectedC9 (mu := mu)) : S2556CorrectedPaperC9Output X mu :=
  { chainA := O.chainA, relaxed := O.source.readout }

def S2559CorrectedC9.Q (O : S2559CorrectedC9 (mu := mu)) : ℝ := O.chainA.Q
def S2559CorrectedC9.Theta (O : S2559CorrectedC9 (mu := mu)) : ℝ := O.source.readout.value
def S2559CorrectedC9.Values (O : S2559CorrectedC9 (mu := mu)) : Set ℝ :=
  {z | ∃ R : RelaxedP6Readout X mu, z = R.value}

theorem S2559CorrectedC9.Q_eq_native (O : S2559CorrectedC9 (mu := mu)) :
    O.Q = LeanFormal.IUT.N8Closure.C9QPilotRegion.qPilotSignedLog X :=
  Q_eq_localScalar X O.chainA |>.trans O.chainA.localData.scalar_eq

theorem S2559CorrectedC9_nonempty
    (hD : Nonempty (P6ChainAData X))
    (R : RelaxedP6Readout X mu)
    (hval : R.value = LeanFormal.IUT.N8Closure.C9QPilotRegion.qPilotSignedLog X) :
    Nonempty (S2559CorrectedC9 (mu := mu)) := by
  obtain ⟨D⟩ := hD
  exact ⟨⟨D, ⟨R, hval⟩⟩⟩

#check S2559CorrectedC9
#check S2559CorrectedC9_nonempty
#print axioms S2559CorrectedC9_nonempty
end LeanFormal.IUT.XiFPaper.S2559CorrectedC9IntegrationActual
end