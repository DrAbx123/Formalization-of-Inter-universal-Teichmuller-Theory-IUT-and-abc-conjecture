import tmp.sheaf.n8.closure.C9PaperClosure
import tmp.sheaf.n8.closure.PaperQLeThetaReduction

/-!
# Paper C9 comparison alias

Reduces the local P6 comparison gap used by PaperQLeThetaReduction to the
upstream C9PaperClosure theorem:

  PaperQLeThetaReduction.missing_paperC9Comparison
    : P6Exact X O.Q OR P6Epsilon X O.Q

and

  C9PaperClosure.paperC9Comparison
    : P6Exact X O.Q OR P6Epsilon X O.Q

have the same PaperC9Output O and the same O.Q.  No chainA alignment is needed:
both statements use exactly O.Q.  Therefore the alias is a direct call, not a
new named gap.  The upstream paperC9Comparison itself remains a named gap.

This file does not edit PaperQLeThetaReduction or C9PaperClosure.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.PaperC9ComparisonAlias

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C9PaperClosure
open LeanFormal.IUT.N8Closure.P6Comparison

universe u

variable {l : PrimeGeFive}

/-- Alias: the PaperQLeThetaReduction P6 comparison gap is exactly the
C9PaperClosure paperC9Comparison theorem, with the same PaperC9Output/Q. -/
theorem paperC9ComparisonAlias
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)]
    (O : C9PaperClosure.PaperC9Output X mu) :
    P6Comparison.P6Exact X O.Q ∨ P6Comparison.P6Epsilon X O.Q :=
  C9PaperClosure.paperC9Comparison (X := X) (mu := mu) O

end LeanFormal.IUT.N8Closure.PaperC9ComparisonAlias
