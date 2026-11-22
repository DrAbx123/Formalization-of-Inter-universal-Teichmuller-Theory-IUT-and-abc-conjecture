/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import tmp.sheaf.gogopex.Iut.Foundations.Species
import tmp.sheaf.gogopex.Iut.Foundations.RealLineCopy
import tmp.sheaf.gogopex.Iut.Foundations.TransportDiagram
import tmp.sheaf.gogopex.Iut.Foundations.IndeterminacyRelation
import tmp.sheaf.gogopex.Iut.Foundations.RegionMeasure
import tmp.sheaf.gogopex.Iut.Foundations.CommonTargetBound
import tmp.sheaf.gogopex.Iut.Foundations.TransportedRegionFamily
import tmp.sheaf.gogopex.Iut.Foundations.QualitativeData
import tmp.sheaf.gogopex.Iut.Foundations.InitialThetaData
import tmp.sheaf.gogopex.Iut.Foundations.AlgorithmicOutput
import tmp.sheaf.gogopex.Iut.Foundations.AlgorithmicBridge
import tmp.sheaf.gogopex.Iut.Stage1.PilotComparison
import tmp.sheaf.gogopex.Iut.Stage1.CorollarySchema
import tmp.sheaf.gogopex.Iut.Stage1.SourceObligations
import tmp.sheaf.gogopex.Iut.Stage1.IUTSourceScaffold
import tmp.sheaf.gogopex.Iut.Stage1.IUTStage1Data
import tmp.sheaf.gogopex.Iut.Stage1.IUTStage1Source
import tmp.sheaf.gogopex.Iut.Stage1.IUTStage1Experiments

/-!
Root module for the IUT formalization corridor.

The root import now exposes the current Stage 1 formal corridor rather than the
early toy/example scaffolding. The main project surface tracks the Corollary
3.12 work.
-/

namespace Iut

def projectName : String := "IUT Lean formalization"

end Iut
