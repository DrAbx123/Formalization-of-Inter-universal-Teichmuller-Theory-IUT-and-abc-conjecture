import tmp.sheaf.xif.paper.S1664FmodODActual
import Mathlib.RingTheory.Ideal.Basic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1671ODSubmoduleActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1664FmodODActual

/-- Actual integer coefficient from the completed-DVR q-candidate order at the
bad place, not an arbitrary choice. -/
noncomputable def s1671Coefficient (l : PrimeGeFive) :
    Bad (S1280Selection l) → ℤ :=
  fun b => ((badPlaceQCandidate (S1280Selection l) b).order : ℤ)

/-- Exact missing O(-D) total: an actual fractional O_Fmod-submodule of Fmod,
represented with Submodule/Ideal (no FractionalIdeal Inv needed), and its
localization to every completion. -/
structure S1671ODSubmoduleData (l : PrimeGeFive) where
  total : Submodule (NumberField.RingOfIntegers (S1280Arithmetic l).Fmod)
    (S1280Arithmetic l).Fmod
  localization : (v : NumberField.FinitePlace (S1280Arithmetic l).Fmod) →
    total → NumberFieldFinitePlace.Completion v

/-- Exact first missing: construct total as the finite intersection/product of
P^{-coeff} and localization by algebraMap. -/
abbrev S1671ODFirstMissing (l : PrimeGeFive) : Type := S1671ODSubmoduleData l

end LeanFormal.IUT.XiFPaper.S1671ODSubmoduleActual
end