import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual

-- Final gate/axiom audit for paper-level xi-f
--
-- This file checks the target proposition and the transport proof conclusion.
-- It does not assert a bridge that is not proved.

-- Target proposition.
#check LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual.ActualPaperXiFTarget
#check LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual.ActualPaperXiFTargetMagnitude

-- Transport proof conclusion.
#check LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual.perBQPilotLog_le_perBThetaHullLog
#check LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual.globalQPilotLog_le_globalThetaHullLog
#check LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual.paperLevelXiFTargetData

-- Axiom audit of the transport proof.
#print axioms LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual.perBQPilotLog_le_perBThetaHullLog
#print axioms LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual.globalQPilotLog_le_globalThetaHullLog
#print axioms LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual.paperLevelXiFTargetData

