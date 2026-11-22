import tmp.sheaf.n8.closure.P6AdmRedesign
import tmp.sheaf.n8.closure.P6ChainA
import tmp.sheaf.n8.closure.NativeC1

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6AdmRedesign
open LeanFormal.IUT.N8Closure.P6ChainA

namespace LeanFormal.IUT.XiFPaper.S2556CorrectedPaperC9OutputActual

universe u
variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]

/-- Corrected C9 output: frozen P6Readout replaced by actual RelaxedP6Readout. -/
structure S2556CorrectedPaperC9Output
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)] where
  chainA : P6ChainAData X
  relaxed : RelaxedP6Readout X mu

namespace S2556CorrectedPaperC9Output

variable {mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v)}
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
variable (O : S2556CorrectedPaperC9Output X mu)

def Q : ℝ := O.chainA.Q
def Theta : ℝ := O.relaxed.value
def Values : Set ℝ := {z | ∃ R : RelaxedP6Readout X mu, z = R.value}

end S2556CorrectedPaperC9Output

variable (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

theorem S2556CorrectedPaperC9Output_nonempty
    (hD : Nonempty (P6ChainAData X))
    [∀ v : NativePlaces X.S, ProperSpace (localFieldAt X v)] :
    Nonempty (S2556CorrectedPaperC9Output X mu) := by
  obtain ⟨D⟩ := hD
  obtain ⟨R⟩ := relaxedP6Readout_actual (X := X) (mu := mu)
  exact ⟨⟨D, R⟩⟩

#check S2556CorrectedPaperC9Output
#check S2556CorrectedPaperC9Output_nonempty
#print axioms S2556CorrectedPaperC9Output_nonempty
end LeanFormal.IUT.XiFPaper.S2556CorrectedPaperC9OutputActual
end