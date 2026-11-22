import tmp.sheaf.xif.paper.Mzk1Example36CorrespondenceLawsActualV2

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1E4Example36ConsumerActualAdapted (adapted copy, A475 reuse) — Example36 correspondence-law consumer

Reuses the EXIT0 Example36 correspondence laws (theta carrier / theater
distinctness / q-membership).  No new math; no closure; gate NOT PASSED.
Registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1E4Example36ConsumerActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Example36CorrespondenceLawsActualV2

theorem example36_thetaCarrier_consumer (l : PrimeGeFive) :
    etthExample36_correspondence_thetaCarrier l :=
  etthExample36_correspondence_thetaCarrier l

theorem example36_theater_distinct_consumer (l : PrimeGeFive) :
    etthExample36_theater_distinct l :=
  etthExample36_theater_distinct l

theorem example36_q_mem_consumer (l : PrimeGeFive) :
    etthExample36_correspondence_q_mem l :=
  etthExample36_correspondence_q_mem l

def e4Example36ConsumerRows : List (String × String × String) :=
  [ ("theta carrier", "example36_thetaCarrier_consumer", "PROVED (reuse)"),
    ("theater distinct", "example36_theater_distinct_consumer", "PROVED (reuse)"),
    ("q membership", "example36_q_mem_consumer", "PROVED (reuse)"),
    ("scope", "no new math; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem e4Example36ConsumerRows_length : e4Example36ConsumerRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1E4Example36ConsumerActualAdapted

end
