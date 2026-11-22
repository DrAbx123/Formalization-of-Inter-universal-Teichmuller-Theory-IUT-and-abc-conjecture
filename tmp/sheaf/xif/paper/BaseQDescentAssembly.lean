import tmp.sheaf.xif.paper.BasePlaceQCandidateActual
import tmp.sheaf.xif.paper.BaseQContractionUnconditional

/-! # Assemble BaseQDescentData from the actual relative norm

The actual relative norm supplies the descent function
relativeNormCompletion : Completion (nativeFPlaceOverBad X) ->
  Completion (nativeBadBasePlace X).

The actual nonzero base q is baseQValue = relativeNormCompletion
(nativeQActual X).q.  What remains for BaseQDescentData is the contraction law
valuation < 1, which is the exact missing LocalNormValuationGap from
BaseQContractionUnconditional.

This file assembles the full BaseQDescentData conditionally on that exact gap,
and the partial actual object unconditionally.  No arbitrary q/axiom/sorry. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.BaseQDescentAssembly

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.BasePlaceQCandidateActual
open LeanFormal.IUT.XiFPaper.RelativeNormCompletion
open LeanFormal.IUT.XiFPaper.BaseQUnconditionalActual
open LeanFormal.IUT.XiFPaper.BaseQContractionUnconditional

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual descent function: the relative norm on completions. -/
noncomputable def baseQDescent : NativeFCompletion (X := X) → NativeBaseCompletion (X := X) :=
  relativeNormCompletion (X := X)

/-- The actual base q value is the descent image of the native q. -/
theorem baseQDescent_nativeQ :
    baseQDescent (X := X) (nativeQActual X).q = baseQValue (X := X) := rfl

/-- The actual descent image is nonzero. -/
theorem baseQDescent_nativeQ_ne_zero :
    baseQDescent (X := X) (nativeQActual X).q ≠ 0 := by
  rw [baseQDescent_nativeQ (X := X)]
  exact baseQValue_ne_zero (X := X)

/-- Unconditional partial assembly: the actual descent function and the
nonzero law.  This is the maximal object assembled without the missing
contraction formula. -/
structure BaseQDescentPartial (X : N8NativeInput l) where
  descent : NativeFCompletion (X := X) → NativeBaseCompletion (X := X)
  q_ne_zero : descent (nativeQActual X).q ≠ 0

/-- The actual partial assembly from the relative norm. -/
noncomputable def baseQDescentPartial : BaseQDescentPartial X where
  descent := baseQDescent (X := X)
  q_ne_zero := baseQDescent_nativeQ_ne_zero (X := X)

/-- Conditional full BaseQDescentData from the exact missing contraction law. -/
noncomputable def baseQDescentDataOfContraction
    (h : NativeQRelativeNormContraction (X := X)) :
    BaseQDescentData (X := X) where
  descent := baseQDescent (X := X)
  q_ne_zero := baseQDescent_nativeQ_ne_zero (X := X)
  valuation_lt_one := h

/-- Conditional full BaseQDescentData from the exact local norm valuation gap
package. -/
noncomputable def baseQDescentDataOfGap
    (h : LocalNormValuationGap (X := X)) :
    BaseQDescentData (X := X) :=
  baseQDescentDataOfContraction (X := X)
    (nativeQRelativeNormContraction_of_gap (X := X) h)

/-- The assembled BaseQDescentData yields the full base-place q candidate. -/
noncomputable def baseQCandidateOfAssembly
    (h : LocalNormValuationGap (X := X)) :
    FinitePlaceQCandidate (nativeBadBasePlace X) :=
  baseQCandidateOfDescent (X := X) (baseQDescentDataOfGap (X := X) h)

/-- The assembled candidate's q is the actual relative norm of nativeQActual. -/
@[simp] theorem baseQCandidateOfAssembly_q
    (h : LocalNormValuationGap (X := X)) :
    (baseQCandidateOfAssembly (X := X) h).q = baseQValue (X := X) := rfl

/-- The exact missing contraction dependency, named explicitly. -/
def MissingContractionDependency : Prop :=
  LocalNormValuationGap (X := X)

/-- The assembled candidate is exactly conditional on the missing contraction
dependency. -/
theorem baseQCandidateOfAssembly_of_missing
    (h : MissingContractionDependency (X := X)) :
    Nonempty (FinitePlaceQCandidate (nativeBadBasePlace X)) :=
  ⟨baseQCandidateOfAssembly (X := X) h⟩

/-! ## Assembly status

Unconditional actual object:

  baseQDescentPartial: descent = relativeNormCompletion, q_ne_zero proved.

Conditional full BaseQDescentData:

  requires NativeQRelativeNormContraction, equivalently the exact
  LocalNormValuationGap (valuation formula + positive-power contraction).

From the gap, the full BaseQDescentData, the base-place FinitePlaceQCandidate,
and its q = baseQValue are assembled.  No arbitrary q/axiom is used. -/

end LeanFormal.IUT.XiFPaper.BaseQDescentAssembly

end
