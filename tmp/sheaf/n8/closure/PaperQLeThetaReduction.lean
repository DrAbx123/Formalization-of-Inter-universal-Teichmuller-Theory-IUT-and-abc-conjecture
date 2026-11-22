import tmp.sheaf.n8.closure.C9PaperClosure
import tmp.sheaf.n8.closure.P6Comparison
import tmp.sheaf.n8.closure.PaperC9ComparisonAttempt
import tmp.sheaf.n8.closure.P6EllOutBridgeAttempt

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# Paper Q <= Theta reduction

Reduces `Q <= Theta` from the P6 exact/epsilon comparison plus ValuesBounded,
conditional on the exact missing interface bridge that every source-allowed
P6 ellOut value is an element of the paper Values set.  Q<=Theta is not an
input and no free assumption is added.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C9QThetaValuesNamed
open LeanFormal.IUT.N8Closure.C9PaperClosure
open LeanFormal.IUT.N8Closure.P6Comparison
open LeanFormal.IUT.N8Closure.PaperC9ComparisonAttempt
open LeanFormal.IUT.N8Closure.P6EllOutBridgeAttempt

namespace LeanFormal.IUT.N8Closure.PaperQLeThetaReduction

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Minimal missing interface bridge: every P6 source-allowed ellOut value is
an element of the paper Values set.  This is strictly weaker than Q<=Theta and
does not mention Q or Theta. -/
def P6EllOutInValues (O : PaperC9Output (X := X) mu) : Prop :=
  ∀ J : P6Comparison.SourceAllowedOutput X,
    J.ellOut ∈ PaperC9Output.valuesSet (X := X) (mu := mu) O

/-- Exact reduction: P6 exact/epsilon + ValuesBounded + the P6->Values bridge
implies Q<=Theta.  No Q<=Theta input. -/
theorem paperQLeTheta_of_comparison_valuesBounded
    (O : PaperC9Output (X := X) mu)
    (hVB : ValuesBounded (X := X) (mu := mu) O)
    (hbridge : P6EllOutInValues (X := X) (mu := mu) O)
    (hcomp : P6Exact X O.Q ∨ P6Epsilon X O.Q) :
    O.Q ≤ O.Theta := by
  rcases hcomp with hExact | hEps
  · obtain ⟨J, _hHull, hQ⟩ := hExact
    rw [← hQ]
    exact hVB J.ellOut (hbridge J)
  · by_contra hnot
    have hgt : O.Theta < O.Q := lt_of_not_ge hnot
    have hε : 0 < (O.Q - O.Theta) / 2 := by linarith
    obtain ⟨J, _hHull, hle⟩ := hEps ((O.Q - O.Theta) / 2) hε
    have hVBJ : J.ellOut ≤ O.Theta := hVB J.ellOut (hbridge J)
    linarith [hle, hVBJ, hgt]

/-- P6 ellOut membership derived via the upstream P6EllOutBridgeAttempt
bridge; the remaining gap moves to the named P6EllOutBridge upstream. -/
theorem missing_p6EllOutInValues
    (O : PaperC9Output (X := X) mu) :
    P6EllOutInValues (X := X) (mu := mu) O :=
  P6EllOutBridgeAttempt.p6EllOutInValues_via_bridge (X := X) (mu := mu) O

/-- P6 comparison derived from the P6 route obligation (no local sorry). -/
theorem paperC9Comparison
    (O : PaperC9Output (X := X) mu) :
    P6Exact X O.Q ∨ P6Epsilon X O.Q :=
  PaperC9ComparisonAttempt.paperC9Comparison_of_route (X := X) (mu := mu) O

/-- Paper Q<=Theta from the route comparison and ValuesBounded, via the
minimal named bridge. -/
theorem paperQLeTheta
    (O : PaperC9Output (X := X) mu)
    (hVB : ValuesBounded (X := X) (mu := mu) O) :
    O.Q ≤ O.Theta :=
  paperQLeTheta_of_comparison_valuesBounded (X := X) (mu := mu) O hVB
    (missing_p6EllOutInValues (X := X) (mu := mu) O)
    (paperC9Comparison (X := X) (mu := mu) O)

end LeanFormal.IUT.N8Closure.PaperQLeThetaReduction

end