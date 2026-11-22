/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier
import tmp.sheaf.xif.paper.Mzk1LogShellCarrierArithmeticActual

/-! # IUT-II log-shell carrier: consumer row index -/

namespace LeanFormal.IUT.XiFPaper.LogShellCarrierIndexActual

/-- Index of the log-shell carrier facts exposed to consumers. -/
def logShellCarrierRows : List (String × String) :=
  [ ("SourceLogShellCarrier.sourceLogShellStar", "def"),
    ("SourceLogShellCarrier.SourceLogShellDatum", "structure"),
    ("SourceLogShellCarrier.SourceLogShellDatum.pStar", "def"),
    ("SourceLogShellCarrier.SourceLogShellDatum.preLogShell", "def"),
    ("SourceLogShellCarrier.SourceLogShellDatum.logShell", "def"),
    ("SourceLogShellCarrier.SourceLogShellDatum.unitLayer", "def"),
    ("SourceLogShellCarrier.SourceLogShellDatum.codomainKummerContained", "def"),
    ("SourceLogShellCarrier.zero_mem_preLogShell", "theorem"),
    ("Mzk1LogShellCarrierArithmeticActual.sourceLogShellStar_dvd", "theorem"),
    ("Mzk1LogShellCarrierArithmeticActual.SourceLogShellDatum.pStar_dvd_sq", "theorem") ]

theorem logShellCarrierRows_length : logShellCarrierRows.length = 10 := rfl

end LeanFormal.IUT.XiFPaper.LogShellCarrierIndexActual
