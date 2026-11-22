import tmp.sheaf.xif.paper.S1688HDDProvenanceSourceActual
import tmp.sheaf.xif.paper.S1402HDDDependentSourceActual

/-! # S1690: faithful HDD output with source image

S1688 showed that SourceDefinition31Data/Input do not carry a q-pilot/theta
output-to-section map.  This file defines the faithful object that would carry
it, gives the actual S1402 image implementation from such a section map, and
proves that the only maps factoring through the current profile/output data are
output-independent.  No inhabitant of the faithful object is asserted. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1690HDDOutputSourceSemanticsActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual
open LeanFormal.IUT.XiFPaper.S1513HDDOutputBindingActual
open LeanFormal.IUT.XiFPaper.S1688HDDProvenanceSourceActual
open LeanFormal.IUT.XiFPaper.S1686HDDProvenanceActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable (s : Finset (NumberField.FinitePlace ℚ))

/-- A section map factoring through the current q/theta profile scalars is
output-independent. -/
noncomputable def S1690ProfileSectionMap
    (factor : Real × Real → S1513DependentPoint s) :
    Theorem311Output I → S1513DependentPoint s :=
  fun _ => factor
    (I.packet.logVolume I.prime.base, I.packet.logVolume I.core.base)

theorem s1690ProfileSectionMap_constant
    (factor : Real × Real → S1513DependentPoint s)
    (o o' : Theorem311Output I) :
    S1690ProfileSectionMap I s factor o =
      S1690ProfileSectionMap I s factor o' :=
  rfl

/-- Faithful output object: it carries an actual q-pilot/theta local-field
section map and the HDD dependent image points.  No inhabitant is asserted. -/
structure S1690HDDOutputWithSourceImage where
  sectionMap : Theorem311Output I → S1513DependentPoint s
  point_ne_zero : ∀ (o) (v : {v : NumberField.FinitePlace ℚ // v ∈ s}),
    sectionMap o v ≠ 0
  integral : ∀ (o) (v : {v : NumberField.FinitePlace ℚ // v ∈ s}),
    sectionMap o v ∈ (CompletionIntegers v.1 : Set (Completion v.1))
  output_dependent : ∃ o o' : Theorem311Output I,
    sectionMap o ≠ sectionMap o'
  detData : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s))

namespace S1690HDDOutputWithSourceImage

variable (H : S1690HDDOutputWithSourceImage (I := I) (s := s))

/-- The actual S1402 dependent HDD source whose image is the singleton of the
source q-pilot/theta section at each output. -/
noncomputable def toSource : S1402DependentHDDSource I s where
  image o := {H.sectionMap o}
  compact_closure o := isCompact_singleton.closure
  nonempty o := ⟨H.sectionMap o, rfl⟩
  coordinate_nonzero o v := ⟨H.sectionMap o, rfl, H.point_ne_zero o v⟩
  detData := H.detData

@[simp] theorem toSource_image (o : Theorem311Output I) :
    H.toSource.image o = {H.sectionMap o} := rfl

end S1690HDDOutputWithSourceImage

/-- The exact source map required: an actual q-pilot/theta output-to-section
map with nonzero integral HDD values and output dependence.  The structure above
is the faithful output object; this alias names its missing source field. -/
abbrev S1690QThetaOutputSectionMapMissing : Type _ :=
  S1690HDDOutputWithSourceImage (I := I) (s := s)

/-- The current honest output record cannot supply a nonconstant source image. -/
theorem s1690HonestOutput_noSourceImage :
    ¬ S1686HonestOutputProvenance (I := I) (s := s) :=
  s1686HonestOutputProvenance_false (I := I) (s := s)

#check S1690ProfileSectionMap
#check s1690ProfileSectionMap_constant
#check S1690HDDOutputWithSourceImage
#check S1690HDDOutputWithSourceImage.toSource
#check S1690HDDOutputWithSourceImage.toSource_image
#check S1690QThetaOutputSectionMapMissing
#check s1690HonestOutput_noSourceImage

end LeanFormal.IUT.XiFPaper.S1690HDDOutputSourceSemanticsActual
end
