/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1FrobeniusUnitsTransportActual
import tmp.sheaf.xif.paper.Mzk1Section0PathCompositionActual
import tmp.sheaf.xif.paper.Mzk1FrobeniusGraphAutClosureActual
import tmp.sheaf.xif.paper.Mzk1LogShellCarrierArithmeticActual
import tmp.sheaf.xif.paper.Mzk1ThetaModLProjectionActual
import tmp.sheaf.xif.paper.Mzk1GraphAutTranslationUnicityActual
import tmp.sheaf.xif.paper.Mzk1FrobeniusPictureArrowFactsActual
import tmp.sheaf.xif.paper.Mzk1ChainTranslationLawActual
import tmp.sheaf.xif.paper.Mzk1AbsoluteKummerTrioSummaryActual

/-!
# IUTI/IUTII skeleton: addenda index (integration import point)

Single import point for the declaration-level addenda written in the DAG prove
loop for the IUTI/IUTII nodes.  The index is purely a consumer convenience: each
entry names the addendum module and the node fragment it belongs to.  No new
mathematical content is asserted beyond the imported modules.

SHEAF node: iuti-ii:Skeleton.AddendaIndex (kind interface, status PENDING-VERIFY
until the DAG watchdog reports EXIT0).
-/

namespace LeanFormal.IUT.XiFPaper.SkeletonAddendaIndexActual

/-- Addendum module (repo path) together with the fragment node it registers. -/
def skeletonAddendaRows : List (String × String) :=
  [ ("tmp/sheaf/xif/paper/Mzk1FrobeniusUnitsTransportActual.lean", "iuti-ii:Frobenius.UnitsTransport"),
    ("tmp/sheaf/xif/paper/Mzk1Section0PathCompositionActual.lean", "iuti-ii:Section0.pathComposition"),
    ("tmp/sheaf/xif/paper/Mzk1FrobeniusGraphAutClosureActual.lean", "iuti-ii:HodgeThetaLinkGraph.closure"),
    ("tmp/sheaf/xif/paper/Mzk1LogShellCarrierArithmeticActual.lean", "iuti-ii:Kummer.LogShellCarrierArithmetic"),
    ("tmp/sheaf/xif/paper/Mzk1ThetaModLProjectionActual.lean", "iuti-ii:Theta.ModLProjection"),
    ("tmp/sheaf/xif/paper/Mzk1GraphAutTranslationUnicityActual.lean", "iuti-ii:HodgeThetaLinkGraph.unicity"),
    ("tmp/sheaf/xif/paper/Mzk1FrobeniusPictureArrowFactsActual.lean", "iuti-ii:HodgeThetaLinkGraph.arrows"),
    ("tmp/sheaf/xif/paper/Mzk1ChainTranslationLawActual.lean", "iuti-ii:HodgeThetaLinkGraph.translationLaw"),
    ("tmp/sheaf/xif/paper/Mzk1AbsoluteKummerTrioSummaryActual.lean", "iuti-ii:IUTII.Kummer.Absolute.summary") ]

theorem skeletonAddendaRows_length : skeletonAddendaRows.length = 9 := rfl

/-- Fragment nodes whose addenda are waiting for a watchdog EXIT0 (status PENDING-VERIFY). -/
def skeletonPendingVerifyNodes : List String :=
  [ "iuti-ii:Frobenius.UnitsTransport",
    "iuti-ii:Section0.pathComposition",
    "iuti-ii:HodgeThetaLinkGraph.closure",
    "iuti-ii:Kummer.LogShellCarrierArithmetic",
    "iuti-ii:Theta.ModLProjection",
    "iuti-ii:HodgeThetaLinkGraph.unicity",
    "iuti-ii:HodgeThetaLinkGraph.arrows",
    "iuti-ii:HodgeThetaLinkGraph.translationLaw",
    "iuti-ii:IUTII.Kummer.Absolute.summary",
    "iuti-ii:Skeleton.AddendaIndex" ]

theorem skeletonPendingVerifyNodes_length : skeletonPendingVerifyNodes.length = 10 := rfl

end LeanFormal.IUT.XiFPaper.SkeletonAddendaIndexActual