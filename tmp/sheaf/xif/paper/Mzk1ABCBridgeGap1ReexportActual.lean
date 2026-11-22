/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ABCBridgeGap1ConsumerActual
import tmp.sheaf.xif.paper.Mzk1ABCBridgeHeightRegionActual

/-! # A606: thin re-export/interface for the Gap-1 lane (no objects changed) -/

/- This file is a declaration-level interface: it re-exports the GREEN Gap-1 consumer
and height-region declarations for ABC Stage 5 consumers, and records their axiom gates.
It introduces no new objects and no new named hypotheses. -/

namespace LeanFormal.IUT.Objects.ABCBridgeGap1Reexport

#check LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap1ConsumerActual.gap1_consumer_comparison
#check LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap1ConsumerActual.epsilonComparisonOfGap1Consumer
#check LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap1ConsumerActual.bridgeInterfaceOfGap1Consumer
#check LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeGap1ConsumerActual.heightBound_of_gap1Consumer
#check LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual.heightRegionGap1Data_object
#check LeanFormal.IUT.XiFPaper.Mzk1ABCBridgeHeightRegionActual.thetaBoundOfHull

end LeanFormal.IUT.Objects.ABCBridgeGap1Reexport
