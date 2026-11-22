/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1429CompletionRootObstructionActual
import tmp.sheaf.n8.closure.SourcePilotRegion
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import tmp.sheaf.xif.paper.Mzk1P2LabelBlockCoefficientActual
noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P2RootChangeOperationActual

open LeanFormal.IUT.XiFPaper.S1429CompletionRootObstructionActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

/-- The old C3 completion carrier is empty: any root-change operation phrased on
it has no inhabitant (S1429 no-go). This is the precise reason the old
`tensorLanding_q`/root-change chain cannot be used. -/
theorem p2RootChange_oldC3_isEmpty
    {l : PrimeGeFive} {V : Type} (I : OriginalInput l V) :
    IsEmpty (SourcePilotRegionData I) :=
  LeanFormal.IUT.XiFPaper.S1429CompletionRootObstructionActual.sourcePilotRegionData_isEmpty I

end LeanFormal.IUT.XiFPaper.Mzk1P2RootChangeOperationActual

end
