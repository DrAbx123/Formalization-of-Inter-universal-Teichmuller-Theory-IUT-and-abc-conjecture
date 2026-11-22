import tmp.sheaf.n8.closure.EtaFPlaceNormalizedComparison
import tmp.sheaf.n8.closure.EtaRssNontrivialActual
import tmp.sheaf.n8.closure.EtaRssSelectedPlaceBridge
import tmp.sheaf.n8.closure.EtaSelectedPlaceReadout

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaRssSourceRegionBridge

universe u

open MeasureTheory BigOperators Set
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open LeanFormal.IUT.N8Closure.EtaRssNontrivialActual
open LeanFormal.IUT.N8Closure.EtaRssSelectedPlaceBridgeRoute
open LeanFormal.IUT.N8Closure.EtaSelectedPlaceReadoutRoute
open LeanFormal.IUT.Foundations.LocalFields.LogShellVolume
open LeanFormal.IUT.NumberFieldFinitePlace

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-! ## Actual source-region quotient data -/

section SourceRegions

variable {K : Type u} [NormedField K] [MeasurableSpace K] [BorelSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable (mu : Measure K) [Measure.IsAddHaarMeasure mu]

noncomputable def sourceClosedRegion : PositiveFiniteRegion K mu :=
  closedRegion (K := K) (mu := mu)

noncomputable def sourceOpenRegion : PositiveFiniteRegion K mu :=
  openRegion (K := K) (mu := mu)

noncomputable def sourceClosedClass : Rss (K := K) mu :=
  Quotient.mk (SameVolume (K := K) mu) (sourceClosedRegion (K := K) (mu := mu))

noncomputable def sourceOpenClass : Rss (K := K) mu :=
  Quotient.mk (SameVolume (K := K) mu) (sourceOpenRegion (K := K) (mu := mu))

theorem sourceClasses_ne : sourceClosedClass (K := K) (mu := mu) ≠
    sourceOpenClass (K := K) (mu := mu) := by
  exact Ne.symm (by
    simpa [sourceClosedClass, sourceOpenClass, sourceClosedRegion, sourceOpenRegion]
      using etaRss_quotient_classes_ne (K := K) (mu := mu))

theorem sourceReadout_ne :
    logVolumeReadout (K := K) (mu := mu) (sourceClosedClass (K := K) (mu := mu)) ≠
      logVolumeReadout (K := K) (mu := mu) (sourceOpenClass (K := K) (mu := mu)) := by
  exact Ne.symm (by
    simpa [sourceClosedClass, sourceOpenClass, sourceClosedRegion, sourceOpenRegion]
      using etaRss_readout_ne (K := K) (mu := mu))

/-- Actual quotient data with two source classes and differing readout. -/
structure SourceRegionQuotientData (K : Type u) [NormedField K]
    [MeasurableSpace K] [BorelSpace K] [IsUltrametricDist K] [ProperSpace K]
    (mu : Measure K) [Measure.IsAddHaarMeasure mu] where
  closedClass : Rss (K := K) mu
  openClass : Rss (K := K) mu
  classes_ne : closedClass ≠ openClass
  readout_ne : logVolumeReadout (K := K) (mu := mu) closedClass ≠
    logVolumeReadout (K := K) (mu := mu) openClass

noncomputable def sourceRegionQuotientData :
    SourceRegionQuotientData K mu where
  closedClass := sourceClosedClass (K := K) (mu := mu)
  openClass := sourceOpenClass (K := K) (mu := mu)
  classes_ne := sourceClasses_ne (K := K) (mu := mu)
  readout_ne := sourceReadout_ne (K := K) (mu := mu)

end SourceRegions

/-! ## F-place shell/selected S data -/

structure EtaFPlaceShellData (X : N8NativeInput l) where
  fShell : SourceLogShellDatum
  fShell_eq : fShell = fPlaceShell X
  fVolumeIndex : Nat
  fVolumeIndex_eq : fVolumeIndex = fPlaceVolumeIndex X
  fLogVolume : Real
  fLogVolume_eq : fLogVolume = fPlaceLogVolume X
  selectedVolumeIndex : Nat
  selectedVolumeIndex_eq : selectedVolumeIndex = etaSelectedVolumeIndex X

noncomputable def etaFPlaceShellData : EtaFPlaceShellData X where
  fShell := fPlaceShell X
  fShell_eq := rfl
  fVolumeIndex := fPlaceVolumeIndex X
  fVolumeIndex_eq := rfl
  fLogVolume := fPlaceLogVolume X
  fLogVolume_eq := rfl
  selectedVolumeIndex := etaSelectedVolumeIndex X
  selectedVolumeIndex_eq := rfl

theorem etaFPlaceShellData_nonempty : Nonempty (EtaFPlaceShellData X) :=
  ⟨etaFPlaceShellData X⟩

/-! ## Source-region/F-place bridge -/

structure EtaRssSourceRegionBridge (X : N8NativeInput l) (K : Type u)
    [NormedField K] [MeasurableSpace K] [BorelSpace K]
    [IsUltrametricDist K] [ProperSpace K]
    (mu : Measure K) [Measure.IsAddHaarMeasure mu] where
  source : SourceRegionQuotientData K mu
  fdata : EtaFPlaceShellData X

noncomputable def etaRssSourceRegionBridge (X : N8NativeInput l) (K : Type u)
    [NormedField K] [MeasurableSpace K] [BorelSpace K]
    [IsUltrametricDist K] [ProperSpace K]
    (mu : Measure K) [Measure.IsAddHaarMeasure mu] :
    EtaRssSourceRegionBridge X K mu where
  source := sourceRegionQuotientData (K := K) (mu := mu)
  fdata := etaFPlaceShellData X

theorem etaRssSourceRegionBridge_nonempty (X : N8NativeInput l) (K : Type u)
    [NormedField K] [MeasurableSpace K] [BorelSpace K]
    [IsUltrametricDist K] [ProperSpace K]
    (mu : Measure K) [Measure.IsAddHaarMeasure mu] :
    Nonempty (EtaRssSourceRegionBridge X K mu) :=
  ⟨etaRssSourceRegionBridge X K mu⟩

/-! ## Exact F-place alignment gap -/

/-- Exact alignment target: the actual F-place log-volume equals the
log-volume readout of the actual closed source-region class. -/
def EtaRssFPlaceAlignmentTarget
    {X : N8NativeInput l} {K : Type u} [NormedField K] [MeasurableSpace K]
    [BorelSpace K] [IsUltrametricDist K] [ProperSpace K]
    {mu : Measure K} [Measure.IsAddHaarMeasure mu]
    (B : EtaRssSourceRegionBridge X K mu) : Prop :=
  B.fdata.fLogVolume = logVolumeReadout (K := K) (mu := mu) B.source.closedClass

end LeanFormal.IUT.N8Closure.EtaRssSourceRegionBridge
