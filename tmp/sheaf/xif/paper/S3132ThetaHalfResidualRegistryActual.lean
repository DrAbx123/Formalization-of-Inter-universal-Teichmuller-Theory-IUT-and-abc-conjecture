import tmp.sheaf.xif.paper.S3132ThetaFactorDimensionActual
import tmp.sheaf.xif.paper.S3132CanonicalVFormValueActual
import tmp.sheaf.xif.paper.S3132ThetaHalfDependencyChainActual
import tmp.sheaf.xif.paper.S1300HDDHullDetActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import tmp.sheaf.xif.paper.C3LogShellTensorHolomorphicHullActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

noncomputable section
open scoped BigOperators

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual
open LeanFormal.IUT.XiFPaper.S3134MainlineRootedHFaActual
open LeanFormal.IUT.XiFPaper.S3134LastSeamExactMissingActual
open LeanFormal.IUT.XiFPaper.S3132Task30ThetaHalfActual
open LeanFormal.IUT.XiFPaper.S3132CanonicalVFormValueActual
open LeanFormal.IUT.XiFPaper.S3132ThetaNormalizationFactorActual
open LeanFormal.IUT.XiFPaper.S3132ThetaHalfDependencyChainActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.S3132ThetaHalfResidualRegistryActual

universe u v uv upi umon ui

/-!
# task-41 registry: the named Theta-half residuals (types + pages)

**Component, not a paper object.**  Owner: hull.  Consumer: the batch-A
registry/gate (mainline + shehdd + lattice).

The sharper paper-faithful Theta target is

    thetaPilotHullLogVolumeReal C3 = S3131CanonicalRootedHC T mu.

By the exact decomposition in `S3132ThetaNormalizationFactorActual`

    thetaPilotHullLogVolumeReal C3 = V(actual paper hull) + thetaNormalizationFactor C3,

it reduces to **two independent named residuals**:

1. `ThetaHalfVFormCanonicalResidual`: `V(actual paper hull) = S3131CanonicalRootedHC T mu`
   — degree-normalized V-form of the actual paper hull equals the canonical
   rooted V-form readout (IUT III, Proposition 3.9, (i), p. 115; Corollary 3.12,
   corpus lines 10324-10353);
2. `ThetaHalfExactFactorResidual`: the exact normalization factor takes the value
   `S3131CanonicalRootedHC T mu - V(actual paper hull)` (equivalently it vanishes
   when residual 1 holds); explicit value in
   `S3132ThetaNormalizationFactorActual.thetaNormalizationFactor_eq`
   (single-factor value in `S3132ThetaFactorDimensionActual`: unit-reference
   log-mass).

The raw readout residual `ThetaHalfRawResidual` (shehdd's last-seam Theta half)
is equivalent to task-30's `MissingFourthTriangleThetaHalfReadout` and does NOT
include the V-form normalization.  The carrier/fiber comparison
(`MissingC3PacketUniformComparison`) is only needed to push
`D.detData.logVolume` to the C3 packet.
-/

/-- Residual A (raw readout): shehdd's last-seam Theta-half identification. -/
def ThetaHalfRawResidual
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (I : Input Label Choice)
    {l : PrimeGeFive} {V0 : Type} {I0 : OriginalInput l V0}
    (C3 : SourcePilotRegionData (l := l) (V := V0) I0)
    (D : S1300HDDHullDetSource I) : Prop :=
  S3134LastSeamThetaHalf (I := I) D C3

/-- Residual 1: the actual V-form of the actual paper hull equals the canonical
rooted V-form readout. -/
def ThetaHalfVFormCanonicalResidual
    {l : PrimeGeFive} {V0 : Type} {I0 : OriginalInput l V0}
    (C3 : SourcePilotRegionData (l := l) (V := V0) I0)
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
    [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)] : Prop :=
  c3NormalizedLogVolume C3
      (actualHolomorphicHull C3 (actualUnitRegion C3)) =
    S3131CanonicalRootedHC T mu

/-- Residual 2 (exact-factor form): the exact normalization factor takes the
canonical-minus-V-form value. -/
def ThetaHalfExactFactorResidual
    {l : PrimeGeFive} {V0 : Type} {I0 : OriginalInput l V0}
    (C3 : SourcePilotRegionData (l := l) (V := V0) I0)
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
    [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)] : Prop :=
  thetaNormalizationFactor C3 =
    S3131CanonicalRootedHC T mu -
      c3NormalizedLogVolume C3
        (actualHolomorphicHull C3 (actualUnitRegion C3))

/-- **Composition:** residuals 1 and 2 give the sharper canonical Theta target. -/
theorem canonicalThetaTarget_of_VForm_and_exactFactor
    {l : PrimeGeFive} {V0 : Type} {I0 : OriginalInput l V0}
    (C3 : SourcePilotRegionData (l := l) (V := V0) I0)
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
    [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]
    (hV : ThetaHalfVFormCanonicalResidual C3 T mu)
    (hf : ThetaHalfExactFactorResidual C3 T mu) :
    thetaPilotHullLogVolumeReal C3 = S3131CanonicalRootedHC T mu := by
  rw [thetaPilotHullLogVolumeReal_eq_normalizedLogVolume_add_factor C3, hf, hV]
  ring

/-- The raw readout residual is exactly task-30's minimal exact missing. -/
theorem thetaHalfRawResidual_iff_missingThetaHalf
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    (I : Input Label Choice)
    {l : PrimeGeFive} {V0 : Type} {I0 : OriginalInput l V0}
    (C3 : SourcePilotRegionData (l := l) (V := V0) I0)
    (D : S1300HDDHullDetSource I) :
    ThetaHalfRawResidual I C3 D ↔
      MissingFourthTriangleThetaHalfReadout (I := I) (I0 := I0) C3 D :=
  S3134LastSeamThetaHalf_iff_missingThetaHalf (I := I) (I0 := I0) C3 D

#check ThetaHalfRawResidual
#check ThetaHalfVFormCanonicalResidual
#check ThetaHalfExactFactorResidual
#check canonicalThetaTarget_of_VForm_and_exactFactor
#check thetaHalfRawResidual_iff_missingThetaHalf

end LeanFormal.IUT.XiFPaper.S3132ThetaHalfResidualRegistryActual

end