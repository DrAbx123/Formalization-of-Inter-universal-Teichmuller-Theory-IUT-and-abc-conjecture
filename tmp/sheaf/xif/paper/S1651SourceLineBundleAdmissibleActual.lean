import tmp.sheaf.xif.paper.S1517SourceLineBundleLocalizationActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1651SourceLineBundleAdmissibleActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual
open LeanFormal.IUT.XiFPaper.S1504SourceLineBundleCarrierActual
open LeanFormal.IUT.XiFPaper.S1517SourceLineBundleLocalizationActual
open ABCBridge.S1423ThetaInvertibleActual
universe u
variable {l : PrimeGeFive}

/-- Admissible source input: an arbitrary SourceDefinition31Data together with
the exact S1517 section localization of the actual S1423 puncture module.
No S1280 K=F native T is used. -/
structure S1651AdmissibleSource (l : PrimeGeFive) where
  source : SourceDefinition31Data.{u} l
  localization : S1517MissingLocalization source

/-- Actual paper line-bundle carrier from the admissible source: total is the
actual S1423 puncture module. -/
noncomputable def s1651Carrier (A : S1651AdmissibleSource (l := l)) :
    PaperLineBundleCarrier (k := A.source.arithmetic.Fmod) :=
  s1517Carrier A.source A.localization

@[simp] theorem s1651Carrier_total (A : S1651AdmissibleSource (l := l)) :
    (s1651Carrier A).total = s1423Module A.source := rfl

theorem s1651Carrier_identified (A : S1651AdmissibleSource (l := l)) :
    PaperLineBundleIdentified A.source (s1651Carrier A) :=
  s1517Carrier_identified A.source A.localization


end LeanFormal.IUT.XiFPaper.S1651SourceLineBundleAdmissibleActual
end