import tmp.sheaf.xif.paper.PaperThetaPilotHullLogVolumeActual
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Paper Theta-pilot mono-analytic normalization: exact obstruction

PaperThetaPilotHullLogVolumeActual constructs the actual Haar measure and raw
hull volume on the F_l^x-indexed Theta-pilot value carrier.  The paper quantity
-|log Theta| requires the mono-analytic normalization:

* an actual mono-analytic unit region O on the paper carrier;
* the Haar normalization of O;
* compactness of the actual hull;
* compatibility of the mono-analytic/Kummer normalization.

The current source tree does not construct the paper's O, its normalization,
or compactness of the F_l^x-indexed actual hull.  This file records the exact
required data; it does not fake normalized log-volume or assert an inequality.

No sorry, axiom, True, or PUnit is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperThetaPilotMonoAnalyticNormalizationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.PaperThetaPilotCarrierActual
open LeanFormal.IUT.XiFPaper.PaperThetaPilotHullLogVolumeActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (q : Real)

/-- The actual F_l^x-indexed paper hull set. -/
abbrev actualPaperHullSet : Set (PaperThetaPilotPoint (l := l)) :=
  paperThetaPilotHullSet (l := l) q

/-- Exact required mono-analytic normalization data on the paper carrier. -/
structure PaperMonoAnalyticNormalizationRequiredData where
  /-- The mono-analytic unit region O on the paper carrier. -/
  unitRegion : Set (PaperThetaPilotPoint (l := l))
  /-- O is measurable. -/
  unitRegion_measurable : MeasurableSet unitRegion
  /-- O is compact. -/
  unitRegion_compact : IsCompact unitRegion
  /-- The actual Haar normalization of O. -/
  unitRegion_normalized : paperThetaPilotHaar (l := l) unitRegion = 1
  /-- The actual paper hull is compact. -/
  hull_compact : IsCompact (actualPaperHullSet (l := l) q)
  /-- The mono-analytic/Kummer normalization is compatible with the hull. -/
  monoAnalytic_compat : Prop

/-- The exact normalization requirement as a proposition. -/
def PaperMonoAnalyticNormalizationRequired : Prop :=
  Nonempty (PaperMonoAnalyticNormalizationRequiredData (l := l) T q)

/-- Actual raw Haar data is available. -/
theorem rawHaar_available :
    Nonempty (Measure (PaperThetaPilotPoint (l := l))) :=
  ⟨paperThetaPilotHaar (l := l)⟩

/-- The raw hull volume is an actual object. -/
theorem rawHullVolume_available :
    Nonempty ENNReal :=
  ⟨paperThetaPilotHullVolume (l := l) q⟩

end LeanFormal.IUT.XiFPaper.PaperThetaPilotMonoAnalyticNormalizationActual

end
