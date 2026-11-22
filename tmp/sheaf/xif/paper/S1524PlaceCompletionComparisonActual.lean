import tmp.sheaf.xif.paper.S1517SourceLineBundleLocalizationActual
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension

/-! # S1524: places above Fmod and completion comparison

For a finite place `v` of `Fmod`, the actual `NumberField.finiteLift` gives a
finite place `w` of `F` with `comap w = v`; `NumberFieldFinitePlace.completionMap`
gives the actual comparison `Completion v -> Completion w`.

These data are NOT enough to localize the S1423 puncture module into
`Completion v`: the module is an ideal of the coordinate ring over `F`, and a
localization needs an actual ring map from that coordinate ring to
`Completion v` (equivalently a point of the curve over `Completion v`).  The
comparison goes the other way (`Completion v -> Completion w`).  The exact
first missing structure is therefore the section-evaluation family
`R ->+* Completion v` for each `v`; it is recorded below and not filled by
zero/constant maps. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1524PlaceCompletionComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1504SourceLineBundleCarrierActual
open LeanFormal.IUT.XiFPaper.S1517SourceLineBundleLocalizationActual
open ABCBridge.S1423ThetaInvertibleActual
open ABCBridge.SourceQlThetaPunctureIdeal

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data.{u} l)

/-- The actual finite place of `F` above `v`, from lying-over. -/
noncomputable def placeAbove (v : NumberField.FinitePlace S.arithmetic.Fmod) :
    NumberField.FinitePlace S.arithmetic.F :=
  NumberFieldPlace.finiteLift (K := S.arithmetic.F) v

theorem comap_placeAbove (v : NumberField.FinitePlace S.arithmetic.Fmod) :
    NumberFieldFinitePlace.comap (k := S.arithmetic.Fmod) (placeAbove S v) = v :=
  NumberFieldPlace.comap_finiteLift (K := S.arithmetic.F) v

/-- The actual completion comparison from the completion at `v` to the
completion at the chosen place above it. -/
noncomputable def completionComparison (v : NumberField.FinitePlace S.arithmetic.Fmod) :
    NumberFieldFinitePlace.Completion v →+*
      NumberFieldFinitePlace.Completion (placeAbove S v) := by
  have h := NumberFieldFinitePlace.completionMap
    (k := S.arithmetic.Fmod) (placeAbove S v)
  rwa [comap_placeAbove] at h

/-- Exact first missing structure: a ring map from the source coordinate ring to
the completion at `v`.  Such a map is the section evaluation/localization; the
place `w | v` and completion comparison alone do not provide it. -/
structure S1524SectionEvaluation (v : NumberField.FinitePlace S.arithmetic.Fmod) where
  eval : sourcePunctureCoordinateRing S →+* NumberFieldFinitePlace.Completion v

/-- A family of exact section evaluations, one for each finite place of Fmod. -/
structure S1524SectionEvaluations where
  eval : (v : NumberField.FinitePlace S.arithmetic.Fmod) →
    S1524SectionEvaluation S v

/-- Given the exact section evaluations, the S1504 localization is defined by
applying the evaluation to the underlying coordinate-ring element of the
puncture module. -/
noncomputable def localizationOfSectionEvaluations
    (E : S1524SectionEvaluations S) : S1504LocalizationData S where
  localization v z := (E.eval v).eval z.1

@[simp] theorem localizationOfSectionEvaluations_apply
    (E : S1524SectionEvaluations S)
    (v : NumberField.FinitePlace S.arithmetic.Fmod) (z : s1423Module S) :
    (localizationOfSectionEvaluations S E).localization v z =
      (E.eval v).eval z.1 := rfl

end LeanFormal.IUT.XiFPaper.S1524PlaceCompletionComparisonActual
end
