import tmp.sheaf.n8.closure.C9PaperClosure
import tmp.sheaf.n8.closure.N8RouteClosure

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# Paper C9 comparison from the P6 route obligation

`C9PaperClosure.paperC9Comparison` was a named sorry.  The P6 route already
has `N8RouteClosure.p6ComparisonObligation X C` for every `P6ChainAData X C`.
Since `PaperC9Output.Q` is definitionally `O.chainA.Q`, the paper comparison
follows directly from the route comparison.  This file records the actual
derivation; it does not modify C9PaperClosure.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open MeasureTheory
open LeanFormal.IUT.N8Closure.C9QThetaValuesNamed
open LeanFormal.IUT.N8Closure.C9PaperClosure
open LeanFormal.IUT.N8Closure.N8RouteClosure
open LeanFormal.IUT.N8Closure.P6Comparison

namespace LeanFormal.IUT.N8Closure.PaperC9ComparisonAttempt

universe u

variable {l : PrimeGeFive} {X : N8NativeInput l}

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  {mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v)}
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Actual derivation of the paper P6 comparison from the route obligation.
J ranges over SourceAllowedOutput X; Q is O.Q = O.chainA.Q. -/
theorem paperC9Comparison_of_route
    (O : PaperC9Output (X := X) mu) :
    P6Comparison.P6Exact X O.Q ∨ P6Comparison.P6Epsilon X O.Q :=
  N8RouteClosure.p6ComparisonObligation X O.chainA

/-- Alias with the original target name, for downstream use. -/
theorem missing_paperC9Comparison_actual
    (O : PaperC9Output (X := X) mu) :
    P6Comparison.P6Exact X O.Q ∨ P6Comparison.P6Epsilon X O.Q :=
  paperC9Comparison_of_route (X := X) (mu := mu) O

end LeanFormal.IUT.N8Closure.PaperC9ComparisonAttempt

end