import tmp.sheaf.xif.paper.S1630HDDOutputImageActual
import tmp.sheaf.xif.paper.S1513HDDOutputBindingActual
import tmp.sheaf.xif.paper.S1551HDDImageGeneratorActual

/-! # S1644: output-dependent HDD point family is not a consequence of the S1402 fields

S1630 reduced the paper image generator to the output-dependent integral point
family `S1630OutputDependentIntegralPoint`.  This file proves that the S1402
image fields alone do not produce that family: for every output-independent
singleton source (in particular S1513's honest singleton source and S1551's
unit reading source), no such family can have that source.  The exact missing
object stays the output-dependent point family itself; no unit reading image
or free lattice is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1644OutputDependentPointActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual
open LeanFormal.IUT.XiFPaper.S1417HDDImageFamilyActual
open LeanFormal.IUT.XiFPaper.S1513HDDOutputBindingActual
open LeanFormal.IUT.XiFPaper.S1551HDDImageGeneratorActual
open LeanFormal.IUT.XiFPaper.S1630HDDOutputImageActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {I : Input Label Choice}
variable {s : Finset (NumberField.FinitePlace ℚ)}

/-- A singleton S1402 source cannot be the source of an output-dependent
S1630 point family: all its images are the same singleton, while the family
requires two different output points. -/
theorem no_outputDependentPoint_of_singletonSource
    (x : S1513DependentPoint s) (hx : ∀ v, x v ≠ 0)
    (det : DetTensorPowerLogVolumeBookkeeping
      (Set (S1513DependentPoint s))) :
    ¬ ∃ P : S1630OutputDependentIntegralPoint (I := I) (s := s),
        P.toSource = s1513SingletonSource (I := I) x hx det := by
  rintro ⟨P, hP⟩
  obtain ⟨o, o', hne⟩ := P.output_dependent
  have hset : ({P.point o} : Set (S1513DependentPoint s)) = {x} := by
    simpa [S1630OutputDependentIntegralPoint.toSource, s1513SingletonSource]
      using congrArg (fun D : S1402DependentHDDSource I s => D.image o) hP
  have hpo : P.point o = x := Set.singleton_eq_singleton_iff.mp hset
  have hset' : ({P.point o'} : Set (S1513DependentPoint s)) = {x} := by
    simpa [S1630OutputDependentIntegralPoint.toSource, s1513SingletonSource]
      using congrArg (fun D : S1402DependentHDDSource I s => D.image o') hP
  have hpo' : P.point o' = x := Set.singleton_eq_singleton_iff.mp hset'
  exact hne (hpo.trans hpo'.symm)

/-- In particular the actual unit-reading source cannot come from an
output-dependent S1630 family. -/
theorem no_outputDependentPoint_of_unitImageSource
    (det : DetTensorPowerLogVolumeBookkeeping
      (Set (S1513DependentPoint s))) :
    ¬ ∃ P : S1630OutputDependentIntegralPoint (I := I) (s := s),
        P.toSource = s1551UnitImageSource (I := I) det := by
  rintro ⟨P, hP⟩
  obtain ⟨o, o', hne⟩ := P.output_dependent
  have hset : ({P.point o} : Set (S1513DependentPoint s)) =
      outputReadingImage I s o := by
    simpa [S1630OutputDependentIntegralPoint.toSource, s1551UnitImageSource]
      using congrArg (fun D : S1402DependentHDDSource I s => D.image o) hP
  have hset' : ({P.point o'} : Set (S1513DependentPoint s)) =
      outputReadingImage I s o' := by
    simpa [S1630OutputDependentIntegralPoint.toSource, s1551UnitImageSource]
      using congrArg (fun D : S1402DependentHDDSource I s => D.image o') hP
  have hread : outputReadingImage I s o = outputReadingImage I s o' :=
    outputReadingImage_output_independent I s o o'
  have hsingle : ({P.point o} : Set (S1513DependentPoint s)) =
      {P.point o'} := hset.trans (hread.trans hset'.symm)
  exact hne (Set.singleton_eq_singleton_iff.mp hsingle)

/-- Exact first missing object, unchanged: the actual output-dependent
integral point family. -/
abbrev S1644FirstMissing : Type _ :=
  S1630OutputDependentIntegralPoint (I := I) (s := s)

#check no_outputDependentPoint_of_singletonSource
#check no_outputDependentPoint_of_unitImageSource
#check S1644FirstMissing

end LeanFormal.IUT.XiFPaper.S1644OutputDependentPointActual
end
