import tmp.sheaf.xif.paper.S1402HDDDependentSourceActual
import tmp.sheaf.xif.paper.S1313IntegralLogShellContractActual

/-!
# S1417: the HDD image family from the actual output / source capsule

S1402 fixes the dependent local-field family E v = oneColumnStructure.localField v
on a finite set s of rational places and defines the hull as
LocalFieldProductHull.hull.  Its exact first field is

  image : Theorem311Output I -> Set ((v : {v // v ∈ s}) -> localField v)

together with compact_closure, nonempty, coordinate_nonzero, and the
DetTensorPowerLogVolumeBookkeeping field.  This file tries the two genuinely
available actual sources and records exactly what they do and do not supply.

1. Actual output side.  theorem311Output I and actualSHEOutput I are actual.
   The only actual output-to-local-field map in the imported SHE/S1402 donor
   chain is the 1-column reading of the unit section, composed with the
   completed-ring localization inclusion.  It is output-independent: readingMap ignores its
   Theorem311Output argument.  Consequently the singleton image built from it
   is a constant family, not the output-dependent HDD image.  The actual
   output-dependent set data is quotientImage I o.quotient : Set Real, which is
   real-valued, not local-field-valued.

2. Actual source-capsule side.  actualIntegralLogShell at an OriginalInput
   place is an actual compact, nonempty, coordinate-nonzero set of the
   common-prime completion.  It has the right HDD shape, but it is attached to
   OriginalInput (number-field places of K), while the S1402 target is over the
   abstract Theorem311Source.Input and the 1-column rational completions
   Completion v.  The imported donor chain supplies no bridge from Input to
   OriginalInput and no place identification.

Thus this file constructs the exact first-field structure and proves its
equivalence with the S1402 source, constructs a conditional source from an
explicit output-to-local-field point map, and records the actual donor facts.
It does not assert an inhabitant of the exact first field, and it does not use
a rank-one / Fin 1 model, an arbitrary Set, True, PUnit, or a new axiom.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1417HDDImageFamilyActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual
open LeanFormal.IUT.XiFPaper.S1313IntegralLogShellContractActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm

universe u v ua uv upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {I : Input Label Choice}
variable {s : Finset (NumberField.FinitePlace ℚ)}

structure S1417ImageFamily (I : Input Label Choice)
    (s : Finset (NumberField.FinitePlace ℚ)) where
  image : Theorem311Output I → Set ((v : {v // v ∈ s}) → S1402DependentE s v)
  compact_closure : ∀ o, IsCompact (closure (image o))
  nonempty : ∀ o, (image o).Nonempty
  coordinate_nonzero : ∀ (o) (v : {v // v ∈ s}), ∃ x ∈ image o, x v ≠ 0
  detData : DetTensorPowerLogVolumeBookkeeping
    (Set ((v : {v // v ∈ s}) → S1402DependentE s v))

namespace S1417ImageFamily

variable {I : Input Label Choice} {s : Finset (NumberField.FinitePlace ℚ)}

def toSource (D : S1417ImageFamily I s) : S1402DependentHDDSource I s where
  image := D.image
  compact_closure := D.compact_closure
  nonempty := D.nonempty
  coordinate_nonzero := D.coordinate_nonzero
  detData := D.detData

def ofSource (D : S1402DependentHDDSource I s) : S1417ImageFamily I s where
  image := D.image
  compact_closure := D.compact_closure
  nonempty := D.nonempty
  coordinate_nonzero := D.coordinate_nonzero
  detData := D.detData

theorem toSource_ofSource (D : S1402DependentHDDSource I s) :
    toSource (ofSource D) = D := by cases D; rfl

theorem ofSource_toSource (D : S1417ImageFamily I s) :
    ofSource (toSource D) = D := by cases D; rfl

def equivSource : S1417ImageFamily I s ≃ S1402DependentHDDSource I s where
  toFun := toSource
  invFun := ofSource
  left_inv := ofSource_toSource
  right_inv := toSource_ofSource

end S1417ImageFamily

/-- The exact first-field type, recorded without an inhabitant. -/
abbrev S1417ImageFamilyRequired (I : Input Label Choice)
    (s : Finset (NumberField.FinitePlace ℚ)) : Type (v + 1) :=
  S1417ImageFamily I s

/-- The exact det-bookkeeping field, exposed separately from the image field.
No inhabitant is supplied. -/
abbrev S1417DetDataRequired (I : Input Label Choice)
    (s : Finset (NumberField.FinitePlace ℚ)) :=
  DetTensorPowerLogVolumeBookkeeping
    (Set ((v : {v // v ∈ s}) → S1402DependentE s v))

noncomputable def outputReadingPoint (I : Input Label Choice)
    (s : Finset (NumberField.FinitePlace ℚ)) (o : Theorem311Output I) :
    ((v : {v // v ∈ s}) → S1402DependentE s v) :=
  fun v => (oneColumnStructure).localizationInclusion v.1
    ((actualSHEOutput I).readingMap v.1 o)

theorem outputReadingPoint_eq_unitSection (I : Input Label Choice)
    (s : Finset (NumberField.FinitePlace ℚ)) (o : Theorem311Output I) :
    outputReadingPoint I s o =
      (fun v : {v // v ∈ s} => (oneColumnStructure).localizationInclusion v.1
        ((actualSHEOutput I).bundle.localization v.1 unitSection)) := rfl

theorem outputReadingPoint_output_independent (I : Input Label Choice)
    (s : Finset (NumberField.FinitePlace ℚ))
    (o o' : Theorem311Output I) :
    outputReadingPoint I s o = outputReadingPoint I s o' := rfl

theorem outputReadingPoint_eq_one (I : Input Label Choice)
    (s : Finset (NumberField.FinitePlace ℚ)) (o : Theorem311Output I)
    (v : {v // v ∈ s}) : outputReadingPoint I s o v = 1 := rfl

theorem outputReadingPoint_ne_zero (I : Input Label Choice)
    (s : Finset (NumberField.FinitePlace ℚ)) (o : Theorem311Output I)
    (v : {v // v ∈ s}) : outputReadingPoint I s o v ≠ 0 := by
  rw [outputReadingPoint_eq_one I s o v]
  exact one_ne_zero

noncomputable def outputReadingImage (I : Input Label Choice)
    (s : Finset (NumberField.FinitePlace ℚ)) (o : Theorem311Output I) :
    Set ((v : {v // v ∈ s}) → S1402DependentE s v) :=
  {outputReadingPoint I s o}

theorem outputReadingImage_compact (I : Input Label Choice)
    (s : Finset (NumberField.FinitePlace ℚ)) (o : Theorem311Output I) :
    IsCompact (closure (outputReadingImage I s o)) :=
  isCompact_singleton.closure

theorem outputReadingImage_nonempty (I : Input Label Choice)
    (s : Finset (NumberField.FinitePlace ℚ)) (o : Theorem311Output I) :
    (outputReadingImage I s o).Nonempty :=
  ⟨outputReadingPoint I s o, rfl⟩

theorem outputReadingImage_coordinate_nonzero (I : Input Label Choice)
    (s : Finset (NumberField.FinitePlace ℚ)) (o : Theorem311Output I)
    (v : {v // v ∈ s}) :
    ∃ x ∈ outputReadingImage I s o, x v ≠ 0 :=
  ⟨outputReadingPoint I s o, rfl, outputReadingPoint_ne_zero I s o v⟩

/-- The actual SHE reading image does not depend on the output. -/
theorem outputReadingImage_output_independent (I : Input Label Choice)
    (s : Finset (NumberField.FinitePlace ℚ))
    (o o' : Theorem311Output I) :
    outputReadingImage I s o = outputReadingImage I s o' := by
  show ({outputReadingPoint I s o} :
    Set ((v : {v // v ∈ s}) → S1402DependentE s v)) =
    {outputReadingPoint I s o'}
  rw [outputReadingPoint_output_independent I s o o']

theorem outputReadingImage_constant (I : Input Label Choice)
    (s : Finset (NumberField.FinitePlace ℚ)) :
    outputReadingImage I s =
      (fun _ => outputReadingImage I s (theorem311Output I)) := by
  funext o
  show ({outputReadingPoint I s o} :
    Set ((v : {v // v ∈ s}) → S1402DependentE s v)) =
    {outputReadingPoint I s (theorem311Output I)}
  rw [outputReadingPoint_output_independent I s o (theorem311Output I)]

structure S1417OutputLocalFieldPoint (I : Input Label Choice)
    (s : Finset (NumberField.FinitePlace ℚ)) where
  point : Theorem311Output I → ((v : {v // v ∈ s}) → S1402DependentE s v)
  point_ne_zero : ∀ (o) (v : {v // v ∈ s}), point o v ≠ 0

namespace S1417OutputLocalFieldPoint

variable {I : Input Label Choice} {s : Finset (NumberField.FinitePlace ℚ)}

noncomputable def image (P : S1417OutputLocalFieldPoint I s) :
    Theorem311Output I → Set ((v : {v // v ∈ s}) → S1402DependentE s v) :=
  fun o => {P.point o}

theorem image_compact (P : S1417OutputLocalFieldPoint I s)
    (o : Theorem311Output I) :
    IsCompact (closure (P.image o)) :=
  isCompact_singleton.closure

theorem image_nonempty (P : S1417OutputLocalFieldPoint I s)
    (o : Theorem311Output I) : (P.image o).Nonempty :=
  ⟨P.point o, rfl⟩

theorem image_coordinate_nonzero (P : S1417OutputLocalFieldPoint I s)
    (o : Theorem311Output I) (v : {v // v ∈ s}) :
    ∃ x ∈ P.image o, x v ≠ 0 :=
  ⟨P.point o, rfl, P.point_ne_zero o v⟩

noncomputable def toImageFamily (P : S1417OutputLocalFieldPoint I s)
    (det : DetTensorPowerLogVolumeBookkeeping
      (Set ((v : {v // v ∈ s}) → S1402DependentE s v))) :
    S1417ImageFamily I s where
  image := P.image
  compact_closure := P.image_compact
  nonempty := P.image_nonempty
  coordinate_nonzero := P.image_coordinate_nonzero
  detData := det

end S1417OutputLocalFieldPoint

noncomputable def outputProfileImage (I : Input Label Choice) :
    Theorem311Output I → Set Real :=
  fun o => quotientImage I o.quotient

theorem outputProfileImage_apply (I : Input Label Choice)
    (o : Theorem311Output I) :
    outputProfileImage I o = quotientImage I o.quotient := rfl

variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

local instance probeValuationFact (vQ : ActualIntegralValuation) :
    Fact vQ.1.Prime := ⟨vQ.2⟩

noncomputable def capsuleLogShell (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace J vQ) : Set (CommonPrimeCompletion v) :=
  (actualIntegralLogShell J vQ v : Set (CommonPrimeCompletion v))

theorem capsuleLogShell_eq (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace J vQ) :
    capsuleLogShell J vQ v =
      (integralLogShell (K := CommonPrimeCompletion v) (p := vQ.1) :
        Set (CommonPrimeCompletion v)) := rfl

theorem capsuleLogShell_nonempty (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace J vQ) :
    (capsuleLogShell J vQ v).Nonempty := by
  refine ⟨1, ?_⟩
  exact one_mem_integralLogShell (K := CommonPrimeCompletion v) (p := vQ.1)

theorem capsuleLogShell_isCompact (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace J vQ) :
    IsCompact (capsuleLogShell J vQ v) := by
  exact isCompact_integralLogShell (K := CommonPrimeCompletion v) (p := vQ.1)

theorem capsuleLogShell_coordinate_nonzero (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace J vQ) :
    ∃ x ∈ capsuleLogShell J vQ v, x ≠ 0 := by
  refine ⟨1, ?_, one_ne_zero⟩
  exact one_mem_integralLogShell (K := CommonPrimeCompletion v) (p := vQ.1)

#check S1417ImageFamily
#check S1417ImageFamilyRequired
#check S1417DetDataRequired
#check S1417ImageFamily.equivSource
#check S1402DependentHDDSource
#check outputReadingPoint
#check outputReadingImage_output_independent
#check outputReadingImage_constant
#check outputProfileImage
#check S1417OutputLocalFieldPoint.toImageFamily
#check capsuleLogShell
#check capsuleLogShell_eq
#check capsuleLogShell_isCompact
#check capsuleLogShell_coordinate_nonzero

end LeanFormal.IUT.XiFPaper.S1417HDDImageFamilyActual