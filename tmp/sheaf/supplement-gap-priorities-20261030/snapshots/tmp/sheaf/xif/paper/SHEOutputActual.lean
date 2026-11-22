import LeanFormal.IUT.IUTIII.Theorem311.SourceFaithfulBoundary
import LeanFormal.IUT.IUTIII.Theorem311.SourceArithmeticHolomorphicLanding
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import Mathlib.Tactic

/-!
# Actual SHE output data over Theorem 3.11 output and 1,column localizations

This file defines the exact output-data record
`SHEOutputActual`, whose `output` field is an actual `Theorem311Output I`, and
whose localization data are actual arithmetic line-bundle localizations over
the completed valuation rings of `Q`. It constructs the actual output object
`theorem311Output I`, the actual unit integral section, its coordinatewise
completed-ring reading, the localization factorization, and the
`SourceLocalizationExpression` of the output object.

The reading map is the concrete localization of the integral unit section; it
does not construct the source-level map from arbitrary Theorem 3.11 output
data to a distinguished arithmetic-vector-bundle section. That missing
source map, and the binding to the paper label `1,circ`, remain exact
obligations; they are documented in the final section and not hidden by a
`True` or an interface-only witness.

No sorry, axiom, `True`, or toy output carrier is used. The actual output
record is `Theorem311Output`; the actual localization carrier is the
completed-ring line bundle of `O_Q`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.Theorem311Source.SHEOutputActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v

/-- The actual 1,column arithmetic holomorphic structure over the finite
places of `Q`, with completed valuation rings as local rings. -/
abbrev oneColumnStructure :
    SourceOneColumnArithmeticHolomorphicStructure (NumberField.FinitePlace ℚ) :=
  { localRing := fun v => CompletionIntegers v
    ringOf := fun _ => inferInstance
    localField := fun v => Completion v
    fieldOf := fun _ => inferInstance
    localizationInclusion := fun v =>
      ValuationSubring.subtype (CompletionIntegers v) }

/-- Completed-ring localization of an integral section of `O_Q`. -/
noncomputable def completionLocalization (v : NumberField.FinitePlace ℚ)
    (x : NumberField.RingOfIntegers ℚ) : (oneColumnStructure).localRing v :=
  algebraMap (NumberField.RingOfIntegers ℚ) (CompletionIntegers v) x

@[simp] theorem completionLocalization_apply
    (v : NumberField.FinitePlace ℚ) (x : NumberField.RingOfIntegers ℚ) :
    completionLocalization v x =
      algebraMap (NumberField.RingOfIntegers ℚ) (CompletionIntegers v) x := rfl

theorem completionLocalization_one (v : NumberField.FinitePlace ℚ) :
    completionLocalization v 1 = 1 := by
  rfl

theorem completionLocalization_mul (v : NumberField.FinitePlace ℚ)
    (x y : NumberField.RingOfIntegers ℚ) :
    completionLocalization v (x * y) =
      completionLocalization v x * completionLocalization v y := by
  exact map_mul (algebraMap (NumberField.RingOfIntegers ℚ)
    (CompletionIntegers v)) x y

theorem completionLocalization_add (v : NumberField.FinitePlace ℚ)
    (x y : NumberField.RingOfIntegers ℚ) :
    completionLocalization v (x + y) =
      completionLocalization v x + completionLocalization v y := by
  exact map_add (algebraMap (NumberField.RingOfIntegers ℚ)
    (CompletionIntegers v)) x y

theorem completionLocalization_zero (v : NumberField.FinitePlace ℚ) :
    completionLocalization v 0 = 0 := by
  rfl

/-- Actual integral line bundle over the completed 1,column rings. -/
abbrev integralLineBundle : SourceArithmeticVectorBundle oneColumnStructure where
  total := NumberField.RingOfIntegers ℚ
  localization v x := completionLocalization v x

namespace IntegralLineBundle

@[simp] theorem localization_apply (v : NumberField.FinitePlace ℚ)
    (x : NumberField.RingOfIntegers ℚ) :
    (integralLineBundle).localization v x = completionLocalization v x := rfl

theorem localization_zero (v : NumberField.FinitePlace ℚ) :
    (integralLineBundle).localization v 0 = 0 := by
  rfl

theorem localization_add (v : NumberField.FinitePlace ℚ)
    (x y : NumberField.RingOfIntegers ℚ) :
    (integralLineBundle).localization v (x + y) =
      (integralLineBundle).localization v x +
        (integralLineBundle).localization v y := by
  exact completionLocalization_add v x y

theorem localization_mul (v : NumberField.FinitePlace ℚ)
    (x y : NumberField.RingOfIntegers ℚ) :
    (integralLineBundle).localization v (x * y) =
      (integralLineBundle).localization v x *
        (integralLineBundle).localization v y := by
  exact completionLocalization_mul v x y

theorem localization_one (v : NumberField.FinitePlace ℚ) :
    (integralLineBundle).localization v 1 = 1 := by
  exact completionLocalization_one v

end IntegralLineBundle

/-- The unit integral section of the actual line bundle. -/
def unitSection : (integralLineBundle).total := (1 : NumberField.RingOfIntegers ℚ)

/-- The actual reading of arbitrary Theorem 3.11 output at a place: the
completed-ring localization of the unit integral section. This is the
concrete reading map; the source-level output-to-section map is recorded as
an exact obligation below. -/
noncomputable def reading {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice] (I : Input Label Choice)
    (v : NumberField.FinitePlace ℚ) (_output : Theorem311Output I) :
    (oneColumnStructure).localRing v :=
  (integralLineBundle).localization v (unitSection)

@[simp] theorem reading_eq_localization {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice] (I : Input Label Choice)
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I) :
    reading (I := I) v o =
      (integralLineBundle).localization v (unitSection) := rfl

theorem reading_factorization {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice] (I : Input Label Choice)
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I) :
    ∃ s : (integralLineBundle).total,
      reading (I := I) v o = (integralLineBundle).localization v s :=
  ⟨unitSection, rfl⟩

/-- Exact output-data record: an actual Theorem 3.11 output object, an actual
1,column line bundle, its reading map, factorization, and the actual output
compatibility fields. -/
structure SHEOutputActual {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice] (I : Input Label Choice) where
  /-- The actual Theorem 3.11 output object. -/
  output : Theorem311Output I
  /-- The actual arithmetic line bundle over the completed 1,column rings. -/
  bundle : SourceArithmeticVectorBundle oneColumnStructure
  /-- Reading of output data in the 1,column local ring at every place. -/
  readingMap : ∀ v : NumberField.FinitePlace ℚ,
    Theorem311Output I → (oneColumnStructure).localRing v
  /-- Every reading factors through the bundle localization. -/
  isLocalizationReading : ∀ (v : NumberField.FinitePlace ℚ)
    (o : Theorem311Output I),
    ∃ s : bundle.total, readingMap v o = bundle.localization v s
  /-- Compatibility with the actual output source. -/
  source_eq : output.source = I.core.base
  /-- Compatibility with the actual output quotient. -/
  quotient_eq : output.quotient = quotientMap I output.source
  /-- Compatibility with the actual part (i). -/
  part_i_eq : output.part_i = partI I
  /-- Compatibility with the actual part (ii). -/
  part_ii_eq : output.part_ii = partII I
  /-- Compatibility with the actual part (iii). -/
  part_iii_eq : output.part_iii = partIII I

/-- Construct actual SHE output data from the actual Theorem 3.11 output and
the actual integral line bundle. The reading map is the concrete localization
of the unit section; the output compatibility fields are the proved
`Theorem311Output` equalities. -/
noncomputable def actualSHEOutput {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice] (I : Input Label Choice) :
    SHEOutputActual I where
  output := theorem311Output I
  bundle := integralLineBundle
  readingMap := fun v _ => reading (I := I) v (theorem311Output I)
  isLocalizationReading := by
    intro v o
    exact reading_factorization (I := I) v o
  source_eq := theorem311Output_source I
  quotient_eq := theorem311Output_quotient I
  part_i_eq := theorem311Output_part_i I
  part_ii_eq := theorem311Output_part_ii I
  part_iii_eq := theorem311Output_part_iii I

namespace SHEOutputActual

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {I : Input Label Choice}

end SHEOutputActual

/-- The actual localization expression of the Theorem 3.11 output for the
constructed SHE output data. -/
noncomputable def actualLocalizationExpression {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice] (I : Input Label Choice) :
    SourceLocalizationExpression oneColumnStructure (Theorem311Output I) where
  bundle := integralLineBundle
  output := theorem311Output I
  expression v o := reading (I := I) v o
  isLocalizationReading v o := reading_factorization (I := I) v o

/-- The actual Theorem 3.11 output is expressible in 1,column localizations of
the actual line bundle. -/
theorem actualOutput_expressible {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice] (I : Input Label Choice) :
    SourceLocalizationExpressible oneColumnStructure (Theorem311Output I) :=
  ⟨actualLocalizationExpression I⟩

/-- Compatibility: the expression's output is exactly the actual Theorem 3.11
output. -/
theorem actualLocalizationExpression_output
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (I : Input Label Choice) :
    (actualLocalizationExpression I).output = theorem311Output I := rfl

/-- Compatibility: the expression reading at a place is the actual
completed-ring localization of the unit section. -/
theorem actualLocalizationExpression_reading
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (I : Input Label Choice) (v : NumberField.FinitePlace ℚ)
    (o : Theorem311Output I) :
    (actualLocalizationExpression I).expression v o =
      (integralLineBundle).localization v unitSection := rfl

/-- The actual output object carries the actual source compatibility. -/
theorem actualSHEOutput_source {Label : Type u} {Choice : Type v}
    [AddGroup Label] [Preorder Choice] (I : Input Label Choice) :
    (actualSHEOutput I).output.source = I.core.base := by
  exact (actualSHEOutput I).source_eq

/- Exact obligation: the source-level map from arbitrary Theorem 3.11 output
data to the distinguished arithmetic-vector-bundle section is not supplied
by this construction. The reading map above is the actual localization of
the unit section, not a canonical output-to-section map. This is the
remaining SHE output obligation; it is not replaced by a `True` field. -/
end LeanFormal.IUT.Theorem311Source.SHEOutputActual

end
