import tmp.sheaf.xif.paper.S1659FmodLineBundleActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1661AdmissibleSourceLineDataActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual
open LeanFormal.IUT.XiFPaper.S1659FmodLineBundleActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
universe u
variable {l : PrimeGeFive}

/-- Faithful admissible source data: arbitrary SourceDefinition31Data together
with an Fmod place map, integral divisor coefficient, O(-D) total type and
localization.  No F-side s1423Module is used. -/
structure S1661AdmissibleSourceData (l : PrimeGeFive) where
  source : SourceDefinition31Data.{u} l
  placeMap : source.badPlaces → NumberField.FinitePlace source.arithmetic.Fmod
  coefficient : source.badPlaces → ℤ
  total : Type u
  localization : (v : NumberField.FinitePlace source.arithmetic.Fmod) →
    total → NumberFieldFinitePlace.Completion v

/-- The exact S1500-style carrier from the admissible data. -/
noncomputable def s1661Carrier
    (A : S1661AdmissibleSourceData.{u} l) :
    PaperLineBundleCarrier (k := A.source.arithmetic.Fmod) where
  total := A.total
  localization := A.localization

@[simp] theorem s1661Carrier_total
    (A : S1661AdmissibleSourceData.{u} l) :
    (s1661Carrier A).total = A.total := rfl

/-- Actual S1280 bad-place map: Bad(S1280Selection l) is a subtype of the
Fmod places V_mod_bad, so its underlying value is an actual finite place. -/
def s1661S1280PlaceMap (l : PrimeGeFive) :
    Bad (S1280Selection l) → NumberField.FinitePlace (S1280Arithmetic l).Fmod :=
  fun b => b.1

/-- Exact first missing for S1280: divisor coefficient/total/localization;
the place map itself is actual above. -/
structure S1661S1280LineData where
  coefficient : Bad (S1280Selection l) → ℤ
  total : Type
  localization : (v : NumberField.FinitePlace (S1280Arithmetic l).Fmod) →
    total → NumberFieldFinitePlace.Completion v

end LeanFormal.IUT.XiFPaper.S1661AdmissibleSourceLineDataActual
end