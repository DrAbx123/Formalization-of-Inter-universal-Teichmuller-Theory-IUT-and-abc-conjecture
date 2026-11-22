import tmp.sheaf.xif.paper.RootHullMeasureActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual

/-!
# Global Theta hull on the product of per-b tensor blocks

The global carrier is the product over the actual bad places of the per-b
normalized tensor blocks.  The global theta hull is the product set of the
per-b root hulls.  The global normalized log-volume is the actual weighted sum
of the per-b root hull log-volumes, with the actual nativeBadLocalWeight.

No single fixed-p Qp tensor block and no sourceSetVolume truncation is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.GlobalThetaHullProductActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Global product carrier: one normalized tensor block per bad place. -/
abbrev globalThetaHullCarrier : Type :=
  (b : Bad (nativePlaceSelection T)) → qVFamTensorBlock T b

/-- Global Theta hull: product of the per-b actual root hulls. -/
def globalThetaHull : Set (globalThetaHullCarrier T) :=
  Set.pi Set.univ (fun b : Bad (nativePlaceSelection T) =>
    rootNormHull (l := l) T b)

/-- Actual per-b measurable structures and Haar measures, supplied as a family. -/
variable (meas : ∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b))
variable (hmeas : ∀ b, BorelSpace (qVFamTensorBlock T b))
variable (mu : ∀ b : Bad (nativePlaceSelection T),
  Measure (qVFamTensorBlock T b))
variable (hmu : ∀ b, Measure.IsAddHaarMeasure (mu b))

/-- Actual per-b root hull normalized log-volume. -/
noncomputable def perBThetaHullLog (b : Bad (nativePlaceSelection T)) : Real :=
  letI : MeasurableSpace (qVFamTensorBlock T b) := meas b
  letI : BorelSpace (qVFamTensorBlock T b) := hmeas b
  letI : Measure.IsAddHaarMeasure (mu b) := hmu b
  rootThetaHullLog (l := l) T b (mu b)

/-- Actual global Theta hull log-volume: weighted sum over the product factors. -/
noncomputable def globalThetaHullLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * perBThetaHullLog T meas hmeas mu hmu b

/-- The global hull log is the weighted sum of the actual per-b logs. -/
theorem globalThetaHullLog_eq :
    globalThetaHullLog T meas hmeas mu hmu =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * perBThetaHullLog T meas hmeas mu hmu b := rfl

end LeanFormal.IUT.XiFPaper.GlobalThetaHullProductActual

end
