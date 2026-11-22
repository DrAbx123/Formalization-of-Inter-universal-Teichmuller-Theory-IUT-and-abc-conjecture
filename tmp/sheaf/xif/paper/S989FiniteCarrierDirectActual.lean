import tmp.sheaf.xif.paper.S978FiniteCarrierHullActual
import tmp.sheaf.xif.paper.S976FiniteLogShellHaarActual
import tmp.sheaf.xif.paper.S975DensityRegionImageActual

/-! # S989: paper tensor directly on the finite log-shell carrier

No topology is installed on FinalLValuedCarrier.  The paper tensor carrier is
Fin d -> Qp, with the actual S976 Haar/unitRegion.  Given a linearization
e : FinalLValuedCarrier ~ Qp^d, transport the region images by e, define the
finite hull, and record the qPilot/hull comparison interface.  Containment is
actual; positivity/finiteness are the exact analytic inputs. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S989FiniteCarrierDirectActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S970FiniteLogShellCarrierActual
open LeanFormal.IUT.XiFPaper.S976FiniteLogShellHaarActual
open LeanFormal.IUT.XiFPaper.S965FinalLCarrierTopologyActual
open LeanFormal.IUT.XiFPaper.S975DensityRegionImageActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open LeanFormal.IUT.XiFPaper.S978FiniteCarrierHullActual
open MeasureTheory Topology

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Actual finite log-shell Haar data on Fin d -> Qp. -/
noncomputable def finitePaperTensorData (d : Nat) :
    FiniteLogShellHaarData (p := qVFamTensorP T b) d :=
  finiteLogShellHaarData (p := qVFamTensorP T b) d

/-- qPilot image on the finite carrier via the linearization. -/
noncomputable def finiteQPilotImage
    (L : S965CarrierLinearization (l := l) T b) :
    Set (FiniteLogShellCarrier (qVFamTensorP T b) L.d) :=
  L.e '' qPilotPaperImageInLValued (l := l) T b

/-- Actual finite paper hull (S978). -/
noncomputable def finitePaperHull
    (L : S965CarrierLinearization (l := l) T b) :
    Set (FiniteLogShellCarrier (qVFamTensorP T b) L.d) :=
  finitePaperTensorHull (T := T) (b := b) L

theorem finiteQPilotImage_subset_finitePaperHull
    (L : S965CarrierLinearization (l := l) T b) :
    finiteQPilotImage (l := l) T b L ⊆ finitePaperHull (l := l) T b L :=
  finiteQPilotImage_subset_finiteHull (T := T) (b := b) L

/-- Normalized log on the finite carrier. -/
noncomputable def finiteNormalizedLog
    {d : Nat} (H : FiniteLogShellHaarData (p := qVFamTensorP T b) d)
    (S : Set (FiniteLogShellCarrier (qVFamTensorP T b) d)) : Real :=
  Real.log (H.measure S).toReal - Real.log (H.measure H.unitRegion).toReal

/-- Comparison interface on the finite carrier. -/
structure FiniteCarrierPaperComparisonInterface where
  linearization : S965CarrierLinearization (l := l) T b
  haarData : FiniteLogShellHaarData (p := qVFamTensorP T b) linearization.d
  qPilotImage : Set (FiniteLogShellCarrier (qVFamTensorP T b) linearization.d)
  hull : Set (FiniteLogShellCarrier (qVFamTensorP T b) linearization.d)
  containment : qPilotImage ⊆ hull
  qPilotLog : Real
  hullLog : Real
  logComparison : Prop

noncomputable def finiteCarrierPaperComparisonInterface
    (L : S965CarrierLinearization (l := l) T b) :
    FiniteCarrierPaperComparisonInterface (l := l) T b where
  linearization := L
  haarData := finitePaperTensorData (l := l) T b L.d
  qPilotImage := finiteQPilotImage (l := l) T b L
  hull := finitePaperHull (l := l) T b L
  containment := finiteQPilotImage_subset_finitePaperHull (l := l) T b L
  qPilotLog := finiteNormalizedLog (T := T) (b := b)
    (finitePaperTensorData (l := l) T b L.d)
    (finiteQPilotImage (l := l) T b L)
  hullLog := finiteNormalizedLog (T := T) (b := b)
    (finitePaperTensorData (l := l) T b L.d)
    (finitePaperHull (l := l) T b L)
  logComparison := finiteNormalizedLog (T := T) (b := b)
      (finitePaperTensorData (l := l) T b L.d) (finiteQPilotImage (l := l) T b L) ≤
    finiteNormalizedLog (T := T) (b := b)
      (finitePaperTensorData (l := l) T b L.d) (finitePaperHull (l := l) T b L)

end LeanFormal.IUT.XiFPaper.S989FiniteCarrierDirectActual
end
