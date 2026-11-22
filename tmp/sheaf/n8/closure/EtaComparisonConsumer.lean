import tmp.sheaf.n8.closure.EtaRouteInterface
import tmp.sheaf.n8.closure.PaperQLeThetaReduction
import Mathlib

/-!
# Eta comparison consumer

The EtaComparison interface gives the actual q-side negativity
(qPilotSignedLog < 0).  The paper normalized Q <= Theta consumer is
PaperQLeThetaReduction.paperQLeTheta, which requires the actual P6 comparison
and ValuesBounded and does not take Q <= Theta as an input.

This file connects the two: Q is identified with EtaNativeQ (the actual native
q scalar) by the exact component EtaQNormalizedIdentification, and EtaComparison
supplies the q-side negativity.  No direct scalar/trivialized-R assumption is
introduced.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C9QThetaValuesNamed
open LeanFormal.IUT.N8Closure.C9PaperClosure
open LeanFormal.IUT.N8Closure.PaperQLeThetaReduction
open LeanFormal.IUT.N8Closure.EtaRouteInterface

namespace LeanFormal.IUT.N8Closure.EtaComparisonConsumer

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Exact normalized identification of the paper Q with the actual native q
scalar.  This is an identification of the actual Eta q-side object, not a free
scalar inequality. -/
def EtaQNormalizedIdentification (O : PaperC9Output (X := X) mu) : Prop :=
  O.Q = EtaNativeQ X

/-- Conditional normalized consumer: EtaComparison plus the exact Q
identification, the actual P6 comparison, and ValuesBounded imply Q <= Theta.
No Q <= Theta assumption is used. -/
theorem etaNormalizedQ_le_Theta
    (O : PaperC9Output (X := X) mu)
    (hEta : EtaComparison X)
    (hQ : EtaQNormalizedIdentification (X := X) (mu := mu) O)
    (hVB : ValuesBounded (X := X) (mu := mu) O) :
    O.Q ≤ O.Theta := by
  have hQneg : O.Q < 0 := by
    rw [hQ]
    exact hEta.2.2
  exact PaperQLeThetaReduction.paperQLeTheta (X := X) (mu := mu) O hVB

end LeanFormal.IUT.N8Closure.EtaComparisonConsumer
