/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.PaperQPilotObjectSourceActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual

/-! # A703/A710: interface record for the parameterized q-pilot readout bridge -/

/- The green constructor is `LeanFormal.IUT.Theorem311Source.paperQPilotObjectSourceActual`
(file paperQPilotObjectSourceActual.lean:61); the S3137 readout is
`qPilotLogVolumeReading : PaperQPilotObjectActual -> Real` (signed q-pilot log-volume).
Bridging them requires the four constructor inputs (boundary/oneColumn/lineBundle/
logKummer) and the T->OriginalInput data bridge (A701 items a,b); this record exposes the
API types only and constructs nothing. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1QPilotReadoutBridgeActual

#check LeanFormal.IUT.Theorem311Source.paperQPilotObjectSourceActual
#check LeanFormal.IUT.Theorem311Source.paperQPilotObjectSourceActual_qPilotLogVolume
#check LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual.qPilotLogVolumeReading
#check LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual.qThetaPilotLogVolumeComparison

end LeanFormal.IUT.XiFPaper.Mzk1QPilotReadoutBridgeActual
