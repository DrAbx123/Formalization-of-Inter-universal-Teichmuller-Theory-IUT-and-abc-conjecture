import tmp.sheaf.xif.paper.S1661AdmissibleSourceLineDataActual
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1664FmodODActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1661AdmissibleSourceLineDataActual
universe u

/-- Actual coefficient choice for S1280 bad places: every bad place gets
coefficient 1.  This is a chosen O(-D) coefficient, not q-order data. -/
def s1664Coefficient (l : PrimeGeFive) :
    Bad (S1280Selection l) → ℤ := fun _ => 1

/-- Exact missing full O(-D) object: an actual FractionalIdeal over the ring
of integers of Fmod together with its localization to every completion. -/
structure S1664FullODData (l : PrimeGeFive) where
  total : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers (S1280Arithmetic l).Fmod)) (S1280Arithmetic l).Fmod
  localization : (v : NumberField.FinitePlace (S1280Arithmetic l).Fmod) →
    total → NumberFieldFinitePlace.Completion v

/-- Exact first missing type: the complete O(-D) FractionalIdeal total plus
localization.  No inhabitant is asserted and no carrier identification is made. -/
abbrev S1664FirstMissing (l : PrimeGeFive) : Type := S1664FullODData l

end LeanFormal.IUT.XiFPaper.S1664FmodODActual
end