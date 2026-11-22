import LeanFormal.IUT.IUTIII.Theorem311.SourceArithmeticHolomorphicLanding
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

/-!
# Actual SHE landing via 1,column localizations of arithmetic line bundles

This file constructs a non-gate SHE landing instance over an actual number
field `k`. The one-column local rings are the completed valuation rings
`CompletionIntegers v`; the arithmetic vector bundle is the actual integral
line bundle of `O_k`-sections; its localization at `v` is the actual algebra
map `O_k → CompletionIntegers v`. Output data are actual integral sections, and
the reading map is the actual completed-ring localization. The resulting
`SourceLocalizationExpression` is not the zero/`PUnit` gate witness: it has a
genuine `O_k` section carrier, genuine completed localizations, and actual
factorization/linearity lemmas. No `True`, `sorry`, or `axiom` is used.

Scope: this is the SHE localization landing data over the actual completion
structure. It does not assert the paper's binding to the label `1,circ`, does
not construct the Theorem 3.11 output object, and does not assert an
IPL/SHE/APT conclusion. The remaining paper-level identifications are those
of `SourceArithmeticHolomorphicLanding.lean`; this file supplies the actual
localization/factorization content over the completion instance.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.Theorem311Source.SHELandingActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

variable {k : Type} [Field k] [NumberField k]

/-- The actual one-column arithmetic holomorphic structure over the finite
places of `k`: completed valuation rings as local rings and adic
completions as local fields. -/
abbrev oneColumnStructure :
    SourceOneColumnArithmeticHolomorphicStructure (NumberField.FinitePlace k) :=
  { localRing := fun v => CompletionIntegers v
    ringOf := fun _ => inferInstance
    localField := fun v => Completion v
    fieldOf := fun _ => inferInstance
    localizationInclusion := fun v =>
      ValuationSubring.subtype (CompletionIntegers v) }

/-- The completed-valuation-ring localization of an integral section at a
finite place. -/
noncomputable def completionLocalization (v : NumberField.FinitePlace k)
    (x : NumberField.RingOfIntegers k) : (oneColumnStructure (k := k)).localRing v :=
  algebraMap (NumberField.RingOfIntegers k) (CompletionIntegers v) x

@[simp] theorem completionLocalization_apply
    (v : NumberField.FinitePlace k) (x : NumberField.RingOfIntegers k) :
    completionLocalization (k := k) v x =
      algebraMap (NumberField.RingOfIntegers k) (CompletionIntegers v) x := rfl

theorem completionLocalization_one (v : NumberField.FinitePlace k) :
    completionLocalization (k := k) v 1 = 1 := by
  rfl

theorem completionLocalization_mul (v : NumberField.FinitePlace k)
    (x y : NumberField.RingOfIntegers k) :
    completionLocalization (k := k) v (x * y) =
      completionLocalization (k := k) v x * completionLocalization (k := k) v y := by
  exact map_mul (algebraMap (NumberField.RingOfIntegers k) (CompletionIntegers v)) x y

theorem completionLocalization_add (v : NumberField.FinitePlace k)
    (x y : NumberField.RingOfIntegers k) :
    completionLocalization (k := k) v (x + y) =
      completionLocalization (k := k) v x + completionLocalization (k := k) v y := by
  exact map_add (algebraMap (NumberField.RingOfIntegers k) (CompletionIntegers v)) x y

theorem completionLocalization_zero (v : NumberField.FinitePlace k) :
    completionLocalization (k := k) v 0 = 0 := by
  rfl

/-- The actual integral line bundle over the 1,column local rings. Its total
space is the ring of integers `O_k`, and its localization at each place is
the actual completed valuation-ring localization. -/
abbrev integralLineBundle : SourceArithmeticVectorBundle (oneColumnStructure (k := k)) where
  total := NumberField.RingOfIntegers k
  localization v x := completionLocalization (k := k) v x

namespace IntegralLineBundle

@[simp] theorem localization_apply (v : NumberField.FinitePlace k)
    (x : NumberField.RingOfIntegers k) :
    (integralLineBundle (k := k)).localization v x =
      completionLocalization (k := k) v x := rfl

theorem localization_zero (v : NumberField.FinitePlace k) :
    (integralLineBundle (k := k)).localization v 0 = 0 := by
  simp [integralLineBundle, completionLocalization]

theorem localization_add (v : NumberField.FinitePlace k)
    (x y : NumberField.RingOfIntegers k) :
    (integralLineBundle (k := k)).localization v (x + y) =
      (integralLineBundle (k := k)).localization v x +
        (integralLineBundle (k := k)).localization v y := by
  simp [integralLineBundle, completionLocalization, map_add]

theorem localization_mul (v : NumberField.FinitePlace k)
    (x y : NumberField.RingOfIntegers k) :
    (integralLineBundle (k := k)).localization v (x * y) =
      (integralLineBundle (k := k)).localization v x *
        (integralLineBundle (k := k)).localization v y := by
  simp [integralLineBundle, completionLocalization, map_mul]

theorem localization_one (v : NumberField.FinitePlace k) :
    (integralLineBundle (k := k)).localization v
      (1 : NumberField.RingOfIntegers k) = 1 := by
  change algebraMap (NumberField.RingOfIntegers k) (CompletionIntegers v) 1 = 1
  simp

end IntegralLineBundle

/-- The actual output carrier for the non-gate landing: an integral section of
the line bundle. -/
abbrev Output (k : Type) [Field k] [NumberField k] : Type :=
  NumberField.RingOfIntegers k

/-- The actual reading of an output section at a finite place. -/
noncomputable def reading (v : NumberField.FinitePlace k)
    (o : Output (k := k)) : (oneColumnStructure (k := k)).localRing v :=
  (integralLineBundle (k := k)).localization v o

@[simp] theorem reading_eq_localization (v : NumberField.FinitePlace k)
    (o : Output (k := k)) :
    reading (k := k) v o = (integralLineBundle (k := k)).localization v o := rfl

theorem reading_zero (v : NumberField.FinitePlace k) :
    reading (k := k) v (0 : Output (k := k)) = 0 := by
  simpa [reading] using
    IntegralLineBundle.localization_zero (k := k) v

theorem reading_add (v : NumberField.FinitePlace k)
    (x y : Output (k := k)) :
    reading (k := k) v (x + y) =
      reading (k := k) v x + reading (k := k) v y := by
  simpa [reading] using IntegralLineBundle.localization_add (k := k) v x y

theorem reading_mul (v : NumberField.FinitePlace k)
    (x y : Output (k := k)) :
    reading (k := k) v (x * y) =
      reading (k := k) v x * reading (k := k) v y := by
  simpa [reading] using IntegralLineBundle.localization_mul (k := k) v x y

/-- Exact localization factorization: every reading is the localization of the
same output section, through the bundle localization map. -/
theorem reading_factorization (v : NumberField.FinitePlace k)
    (o : Output (k := k)) :
    ∃ s : (integralLineBundle (k := k)).total,
      reading (k := k) v o = (integralLineBundle (k := k)).localization v s :=
  ⟨o, rfl⟩

/-- The actual localization expression of an output section: the output datum
is the integral section, and the expression at every place is its actual
completed-ring localization, factorized through the bundle. -/
noncomputable def outputLocalizationExpression (o : Output (k := k)) :
    SourceLocalizationExpression (oneColumnStructure (k := k)) (Output (k := k)) where
  bundle := integralLineBundle (k := k)
  output := o
  expression v o' := reading (k := k) v o'
  isLocalizationReading v o' := reading_factorization (k := k) v o'

/-- The non-gate SHE landing instance for actual integral section output. -/
theorem sourceLocalizationExpressible_integralSection (o : Output (k := k)) :
    SourceLocalizationExpressible (oneColumnStructure (k := k))
      (Output (k := k)) :=
  ⟨outputLocalizationExpression (k := k) o⟩

/-- The expression map is exactly the bundle localization on the integral
section carrier. -/
theorem expression_eq_bundle_localization (o : Output (k := k))
    (v : NumberField.FinitePlace k) :
    (outputLocalizationExpression (k := k) o).expression v o =
      (outputLocalizationExpression (k := k) o).bundle.localization v o := rfl

/-- The expression map is additive in the output section. -/
theorem expression_add (v : NumberField.FinitePlace k)
    (x y : Output (k := k)) :
    (outputLocalizationExpression (k := k) x).expression v (x + y) =
      reading (k := k) v x + reading (k := k) v y := by
  exact reading_add (k := k) v x y

/-- The expression map is multiplicative in the integral section ring. -/
theorem expression_mul (v : NumberField.FinitePlace k)
    (x y : Output (k := k)) :
    (outputLocalizationExpression (k := k) x).expression v (x * y) =
      reading (k := k) v x * reading (k := k) v y := by
  exact reading_mul (k := k) v x y

/-- The zero section is an actual output with zero reading at every place. -/
theorem zero_reading (v : NumberField.FinitePlace k) :
    (outputLocalizationExpression (k := k) 0).expression v 0 = 0 := by
  exact reading_zero (k := k) v

/-- The total space is the actual ring of integers, not the one-point gate
carrier. -/
theorem total_eq_ringOfIntegers :
    (integralLineBundle (k := k)).total = NumberField.RingOfIntegers k := rfl

/-- A concrete nonzero output section: `1` in `O_k`. -/
def unitOutput : Output (k := k) := 1

theorem unitOutput_reading (v : NumberField.FinitePlace k) :
    reading (k := k) v (unitOutput (k := k)) = 1 := by
  simpa [unitOutput, reading] using
    IntegralLineBundle.localization_one (k := k) v

/-- Non-gate landing witness: an actual line bundle over the completed
1,column rings, an actual integral output section, actual reading maps, and
exact factorization through the bundle localization. -/
theorem completionSHELanding_nonGate :
    ∃ (B : SourceArithmeticVectorBundle (oneColumnStructure (k := k)))
      (O : Type) (o : O)
      (e : ∀ v : NumberField.FinitePlace k, O → (oneColumnStructure (k := k)).localRing v),
      (∀ (v : NumberField.FinitePlace k) (o' : O),
        ∃ s : B.total, e v o' = B.localization v s) := by
  refine ⟨integralLineBundle (k := k), Output (k := k), unitOutput (k := k),
    (fun v (o' : Output (k := k)) => reading (k := k) v o'), ?_⟩
  intro v o'
  exact ⟨o', rfl⟩

end LeanFormal.IUT.Theorem311Source.SHELandingActual

end
