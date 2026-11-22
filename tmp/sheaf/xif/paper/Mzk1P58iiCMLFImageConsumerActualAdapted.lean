import tmp.sheaf.xif.paper.Mzk1P58iiCMLFImageActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1P58iiCMLFImageConsumerActualAdapted (adapted copy, A475 reuse) — P58ii CMLF image consumers

Reuses the EXIT0 P58ii CMLF image laws: invariant-preserving CMLF morphisms preserve
unit layer, pre-log-shell and (under p-star compatibility) log-shell.  No new math;
no closure; gate NOT PASSED; registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1P58iiCMLFImageConsumerActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P58iiCMLFImageActual

universe u

theorem p58ii_cmlf_image_unitLayer_consumer {D E : SourceLogShellDatum.{u}}
    (f : CMLFInvariantHom D E) :
    f.toCMLFHom.mapK '' D.unitLayer ⊆ E.unitLayer :=
  CMLFInvariantHom.image_unitLayer f

theorem p58ii_cmlf_image_preLogShell_consumer {D E : SourceLogShellDatum.{u}}
    (f : CMLFInvariantHom D E) :
    f.toCMLFHom.mapK '' D.preLogShell ⊆ E.preLogShell :=
  CMLFInvariantHom.image_preLogShell f

theorem p58ii_cmlf_image_logShell_consumer {D E : SourceLogShellDatum.{u}}
    (f : CMLFInvariantHom D E) (hstar : D.pStar = E.pStar) :
    f.toCMLFHom.mapK '' D.logShell ⊆ E.logShell :=
  CMLFInvariantHom.image_logShell f hstar

def p58iiCMLFImageConsumerRows : List (String × String × String) :=
  [ ("unit layer", "p58ii_cmlf_image_unitLayer_consumer", "PROVED (reuse)"),
    ("pre-log-shell", "p58ii_cmlf_image_preLogShell_consumer", "PROVED (reuse)"),
    ("log-shell", "p58ii_cmlf_image_logShell_consumer", "PROVED (reuse under p-star)"),
    ("scope", "no new math; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem p58iiCMLFImageConsumerRows_length : p58iiCMLFImageConsumerRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P58iiCMLFImageConsumerActualAdapted

end
