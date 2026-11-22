import tmp.sheaf.xif.paper.PaperThetaPilotMonoAnalyticNormalizationActual

/-!
# Paper F_l^x Theta-pilot normalized hull volume: actual candidate

This file works on the actual F_l^x paper Theta-pilot carrier of
PaperThetaPilotCarrierActual and the actual Haar measure
paperThetaPilotHaar of PaperThetaPilotHullLogVolumeActual.

It constructs an actual unit region: the image under the actual
log-coordinate equivalence paperThetaPilotToAdd of the product box
[0,1] over the F_l^x labels. It then defines the actual Haar volume of this
unit region and the actual candidate

  normalizedHullVolume q = hullVolume q / unitRegionVolume,
  normalizedHullLogVolume q = log normalizedHullVolume q.

These are actual definitions using the actual Haar measure; no normalization
value is asserted.

Exact remaining obstruction data, kept as propositions without inhabitants:
* the Haar volume of the unit region is 1;
* the actual paper hull is compact;
* the mono-analytic/Kummer compatibility relation.

The file therefore constructs the actual candidate and records precisely what
is missing, without faking the paper normalization or any inequality.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperThetaPilotNormalizedVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.PaperThetaPilotCarrierActual
open LeanFormal.IUT.XiFPaper.PaperThetaPilotHullLogVolumeActual
open LeanFormal.IUT.XiFPaper.PaperThetaPilotMonoAnalyticNormalizationActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual product box [0,1] in the F_l^x log-coordinate space. -/
def paperUnitBox : Set (PaperThetaPilotCarrier (l := l) → Real) :=
  Set.pi Set.univ (fun _ => Set.Icc (0 : Real) 1)

/-- The actual unit region on the paper carrier: the image of the log-coordinate
box under the actual equivalence paperThetaPilotToAdd. -/
noncomputable def paperUnitRegion : Set (PaperThetaPilotPoint (l := l)) :=
  (paperThetaPilotToAdd (l := l)).symm '' paperUnitBox (l := l)

/-- The actual Haar volume of the unit region. -/
noncomputable def paperUnitRegionVolume : ENNReal :=
  paperThetaPilotHaar (l := l) paperUnitRegion

/-- The actual candidate normalized hull volume. -/
noncomputable def paperNormalizedHullVolume (q : Real) : ENNReal :=
  paperThetaPilotHullVolume (l := l) q /
    paperUnitRegionVolume (l := l)

/-- The actual candidate normalized hull log-volume. -/
noncomputable def paperNormalizedHullLogVolume (q : Real) : Real :=
  Real.log (paperNormalizedHullVolume (l := l) q).toReal

/-- The actual candidate data: unit region, its Haar volume, and the normalized
hull volume/log-volume. -/
structure PaperNormalizedHullCandidate where
  unitRegion : Set (PaperThetaPilotPoint (l := l))
  unitRegionVolume : ENNReal
  normalizedHullVolume : ENNReal
  normalizedHullLogVolume : Real
  unitRegion_eq : unitRegion = paperUnitRegion (l := l)
  unitRegionVolume_eq : unitRegionVolume = paperUnitRegionVolume (l := l)
  normalizedHullVolume_eq : normalizedHullVolume =
    paperNormalizedHullVolume (l := l) (0 : Real)
  normalizedHullLogVolume_eq : normalizedHullLogVolume =
    paperNormalizedHullLogVolume (l := l) (0 : Real)

/-- Actual normalization candidate at q = 0. -/
noncomputable def paperNormalizedHullCandidate :
    PaperNormalizedHullCandidate (l := l) T where
  unitRegion := paperUnitRegion (l := l)
  unitRegionVolume := paperUnitRegionVolume (l := l)
  normalizedHullVolume := paperNormalizedHullVolume (l := l) 0
  normalizedHullLogVolume := paperNormalizedHullLogVolume (l := l) 0
  unitRegion_eq := rfl
  unitRegionVolume_eq := rfl
  normalizedHullVolume_eq := rfl
  normalizedHullLogVolume_eq := rfl

/-- Exact obstruction 1: the actual unit region has Haar volume one. -/
def PaperUnitRegionNormalizedObstruction : Prop :=
  paperUnitRegionVolume (l := l) = 1

/-- Exact obstruction 2: the actual F_l^x hull is compact. -/
def PaperHullCompactObstruction (q : Real) : Prop :=
  IsCompact (paperThetaPilotHullSet (l := l) q)

/-- Exact obstruction 3: the mono-analytic/Kummer normalization compatibility
of the paper carrier. This is the source compatibility relation, recorded as a
proposition, not replaced by a definitional identity. -/
def PaperMonoAnalyticCompatibilityObstruction : Prop :=
  PaperMonoAnalyticNormalizationRequired (l := l) T 0

/-- Exact normalization obstruction package. -/
def PaperNormalizedHullObstruction (q : Real) : Prop :=
  PaperUnitRegionNormalizedObstruction (l := l) ∧
    PaperHullCompactObstruction (l := l) q ∧
    PaperMonoAnalyticCompatibilityObstruction (l := l) T

/-- The normalized candidate is actual; its paper normalization conditions are
the exact propositions above. -/
theorem paperNormalizedHullCandidate_actual :
    Nonempty (PaperNormalizedHullCandidate (l := l) T) :=
  ⟨paperNormalizedHullCandidate (l := l) T⟩

end LeanFormal.IUT.XiFPaper.PaperThetaPilotNormalizedVolumeActual

end
