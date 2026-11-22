import tmp.sheaf.xif.paper.S1551HDDImageGeneratorActual
import tmp.sheaf.xif.paper.S1417HDDImageFamilyActual
import tmp.sheaf.xif.paper.S1402HDDDependentSourceActual

/-! # S1630: output-dependent integral HDD image generator

S1551 reduced the paper-level HDD image generator to an actual output-dependent
source plus one integral nonzero image point per output and place.  This file
constructs that reduction from an explicit actual point family
`S1630OutputDependentIntegralPoint`, and records that family as the exact
first missing structure.  No unit reading image, free lattice or rank-one
surrogate is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1630HDDOutputImageActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual
open LeanFormal.IUT.XiFPaper.S1417HDDImageFamilyActual
open LeanFormal.IUT.XiFPaper.S1513HDDOutputBindingActual
open LeanFormal.IUT.XiFPaper.S1551HDDImageGeneratorActual
open LeanFormal.IUT.XiFPaper.S1500HDDOutputDependentActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {I : Input Label Choice}
variable {s : Finset (NumberField.FinitePlace ℚ)}

/-- Exact first missing structure: an actual output-dependent family of
nonzero integral points in the dependent local-field product. -/
structure S1630OutputDependentIntegralPoint where
  point : Theorem311Output I → S1513DependentPoint s
  point_ne_zero : ∀ (o) (v : {v : NumberField.FinitePlace ℚ // v ∈ s}),
    point o v ≠ 0
  integral : ∀ (o) (v : {v : NumberField.FinitePlace ℚ // v ∈ s}),
    point o v ∈ (CompletionIntegers v.1 : Set (Completion v.1))
  output_dependent : ∃ (o o' : Theorem311Output I), point o ≠ point o'
  detData : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s))

namespace S1630OutputDependentIntegralPoint

variable (P : S1630OutputDependentIntegralPoint (I := I) (s := s))

/-- The actual S1402 source whose image at `o` is the singleton of the
output-dependent point. -/
noncomputable def toSource : S1402DependentHDDSource I s where
  image o := {P.point o}
  compact_closure o := isCompact_singleton.closure
  nonempty o := ⟨P.point o, rfl⟩
  coordinate_nonzero o v := ⟨P.point o, rfl, P.point_ne_zero o v⟩
  detData := P.detData

@[simp] theorem toSource_image (o : Theorem311Output I) :
    P.toSource.image o = {P.point o} := rfl

/-- The S1551 integral image-point datum associated with the family. -/
noncomputable def toIntegralImagePoint :
    S1551IntegralImagePoint P.toSource where
  point o v := P.point o
  mem o v := by simp
  integral o v := P.integral o v
  nonzero o v := P.point_ne_zero o v

/-- The paper-level output-dependent HDD image generator. -/
noncomputable def toPaperImageGenerator :
    S1551HDDPaperImageGenerator (I := I) (s := s) where
  source := P.toSource
  generator := P.toIntegralImagePoint
  image_output_dependent := by
    rcases P.output_dependent with ⟨o, o', hne⟩
    refine ⟨o, o', ?_⟩
    intro hset
    have hset' : ({P.point o} : Set (S1513DependentPoint s)) = {P.point o'} := hset
    exact hne (Set.singleton_eq_singleton_iff.mp hset')

end S1630OutputDependentIntegralPoint

/-- The exact first missing structure is this output-dependent integral point
family; S1551's paper image generator is constructed from it. -/
def S1630FirstMissing : Type _ :=
  S1630OutputDependentIntegralPoint (I := I) (s := s)

#check S1630OutputDependentIntegralPoint
#check S1630OutputDependentIntegralPoint.toSource
#check S1630OutputDependentIntegralPoint.toPaperImageGenerator
#check S1630FirstMissing

end LeanFormal.IUT.XiFPaper.S1630HDDOutputImageActual
end
