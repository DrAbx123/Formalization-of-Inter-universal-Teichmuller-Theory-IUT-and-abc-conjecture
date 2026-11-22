import tmp.sheaf.xif.paper.S1651SourceLineBundleAdmissibleActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import tmp.sheaf.xif.paper.PaperLineBundleCarrierBase

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1659FmodLineBundleActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual
universe u
variable {l : PrimeGeFive}

/-- Exact first missing Fmod-side line-bundle data: a place map from the bare
badPlaces type, an integral divisor coefficient, the O(-D) section type at
Fmod, and its localization into every completion of Fmod.  No s1423Module is
used. -/
structure S1659FmodLineBundleData (S : SourceDefinition31Data.{u} l) where
  placeMap : S.badPlaces → NumberField.FinitePlace S.arithmetic.Fmod
  coefficient : S.badPlaces → ℤ
  /-- The actual O(-D) section type over Fmod. -/
  total : Type u
  /-- Localization of sections to every completion of Fmod. -/
  localization : (v : NumberField.FinitePlace S.arithmetic.Fmod) →
    total → NumberFieldFinitePlace.Completion v

/-- Conditional paper line-bundle carrier on the exact Fmod-side data. -/
noncomputable def s1659Carrier
    (S : SourceDefinition31Data.{u} l) (D : S1659FmodLineBundleData S) :
    PaperLineBundleCarrier (k := S.arithmetic.Fmod) where
  total := D.total
  localization := D.localization

@[simp] theorem s1659Carrier_total
    (S : SourceDefinition31Data.{u} l) (D : S1659FmodLineBundleData S) :
    (s1659Carrier S D).total = D.total := rfl

/-- Exact place map target: bare badPlaces must be mapped to Fmod places. -/
def S1659PlaceMapRequired (S : SourceDefinition31Data.{u} l) : Prop :=
  Nonempty (S.badPlaces → NumberField.FinitePlace S.arithmetic.Fmod)

end LeanFormal.IUT.XiFPaper.S1659FmodLineBundleActual
end