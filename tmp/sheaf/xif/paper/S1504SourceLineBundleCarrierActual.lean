import tmp.sheaf.xif.paper.S1423ThetaInvertibleActual
import tmp.sheaf.xif.paper.PaperLineBundleCarrierBase
import tmp.sheaf.xif.PaperQPilotObject

/-! # S1504: paper line-bundle carrier from the actual S1423 puncture module

S1497 shows no native donor D.  S1423 supplies the actual puncture module
`s1423Module S` (rank-one projective/invertible, finrank 1) and the actual
Picard line bundle `s1423LineBundle S`.  This file builds the paper carrier
with total exactly that module section type.

The localization from an arbitrary coordinate-ring section to the completion
of `Fmod` is NOT in S1423: the module is an ideal of the coordinate ring over
`S.arithmetic.F`, while the paper completion is at a place of
`S.arithmetic.Fmod`.  An actual localization map is therefore the exact first
field; it is represented below as explicit data, not by zero or a constant map.

Given that data, `PaperLineBundleCarrier` and the `PaperQPilotObject.lineBundle`
update are constructed, and the identification proposition is the actual
equality `carrier.total = s1423Module S`, proved by rfl. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1504SourceLineBundleCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual
open ABCBridge.S1423ThetaInvertibleActual

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data.{u} l)

/-- Exact missing localization data: for each finite place of the modified
field, a localization of the actual S1423 puncture module into the completion
field.  This is the precise map S1423 does not provide. -/
structure S1504LocalizationData where
  localization : (v : NumberField.FinitePlace S.arithmetic.Fmod) →
    s1423Module S → NumberFieldFinitePlace.Completion v

/-- The paper carrier with total exactly the actual puncture module, conditional
on the exact localization data. -/
noncomputable def carrierOfLocalization (L : S1504LocalizationData S) :
    PaperLineBundleCarrier (k := S.arithmetic.Fmod) where
  total := s1423Module S
  localization := L.localization

@[simp] theorem carrierOfLocalization_total (L : S1504LocalizationData S) :
    (carrierOfLocalization S L).total = s1423Module S := rfl

/-- The actual paper line-bundle identification: the carrier's section type is
the S1423 puncture module. -/
def PaperLineBundleIdentified (C : PaperLineBundleCarrier (k := S.arithmetic.Fmod)) : Prop :=
  C.total = s1423Module S

theorem carrierOfLocalization_identified (L : S1504LocalizationData S) :
    PaperLineBundleIdentified S (carrierOfLocalization S L) := rfl


section QPilot

open LeanFormal.IUT.XiFPaper

universe uv uL uC uG

variable {V : Type uv} {Label : Type uL} {Choice : Type uC}
  [AddGroup Label] [Preorder Choice]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable (I : OriginalInput.{u, uv, 0, 0, 0} l V)
variable (envStrip : FPrimeStrip V)

/-- Replace the opaque line-bundle slot of a paper q-pilot object by the actual
S1423-module carrier (conditional on the exact localization data). -/
noncomputable def fillQPilotObject
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (L : S1504LocalizationData I.initial) :
    PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip where
  boundary := O.boundary
  strip := O.strip
  strip_eq_source := O.strip_eq_source
  oneColumn := O.oneColumn
  lineBundle := carrierOfLocalization I.initial L
  logKummer := O.logKummer
  qPilotLogVolume := O.qPilotLogVolume
  qPilotLogVolume_eq := O.qPilotLogVolume_eq
  paper_strip_identification := O.paper_strip_identification
  paper_lineBundle_identification :=
    PaperLineBundleIdentified I.initial (carrierOfLocalization I.initial L)
  paper_logKummer_identification := O.paper_logKummer_identification
  paper_qPilot_log_identification := O.paper_qPilot_log_identification

@[simp] theorem fillQPilotObject_lineBundle
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (L : S1504LocalizationData I.initial) :
    (fillQPilotObject (I := I) (G := G) (envStrip := envStrip) O L).lineBundle =
      carrierOfLocalization I.initial L := rfl

/-- The filled object's paper line-bundle identification is the actual equality
of its section type with the S1423 puncture module. -/
theorem fillQPilotObject_paper_lineBundle_identification
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (L : S1504LocalizationData I.initial) :
    (fillQPilotObject (I := I) (G := G) (envStrip := envStrip) O L).paper_lineBundle_identification :=
  carrierOfLocalization_identified I.initial L

end QPilot

end LeanFormal.IUT.XiFPaper.S1504SourceLineBundleCarrierActual
end
