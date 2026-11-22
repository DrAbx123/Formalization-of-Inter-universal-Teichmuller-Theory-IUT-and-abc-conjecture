import tmp.sheaf.xif.paper.PaperThetaPilotCarrierActual
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Actual Haar volume candidate on the F_l^x-indexed Theta-pilot hull

The paper Theta-pilot carrier of PaperThetaPilotCarrierActual is

  PaperThetaPilotPoint = F_l^x -> Multiplicative Real.

This file constructs an actual additive Haar measure on the log-coordinate
space F_l^x -> Real and transports it to the multiplicative value carrier by
the actual equivalence Multiplicative.toAdd.  It then defines the actual
measure and log-volume of the actual paper hull paperThetaPilotHull q.

The paper quantity -|log Theta| is the **mono-analytic normalized** hull
log-volume; this file constructs the actual Haar volume candidate but does not
assert the mono-analytic normalization, unit-region normalization, or hull
compactness.  Those are the exact missing normalization data, not replaced by
the raw theta-value sum.

No sorry, axiom, True, or PUnit is used. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperThetaPilotHullLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.PaperThetaPilotCarrierActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Actual equiv from the multiplicative value carrier to its log coordinates. -/
def paperThetaPilotToAdd :
    PaperThetaPilotPoint (l := l) ≃
      (PaperThetaPilotCarrier (l := l) -> Real) where
  toFun x j := (x j).toAdd
  invFun f j := Multiplicative.ofAdd (f j)
  left_inv x := by
    funext j
    simp
  right_inv f := by
    funext j
    simp

/-- Actual Haar measure on the F_l^x log-coordinate space, transported to the
multiplicative paper Theta-pilot carrier. -/
noncomputable def paperThetaPilotHaar :
    Measure (PaperThetaPilotPoint (l := l)) :=
  Measure.map (paperThetaPilotToAdd (l := l)).symm
    (Measure.addHaar : Measure (PaperThetaPilotCarrier (l := l) -> Real))

/-- The actual paper hull as a set on the value carrier. -/
noncomputable def paperThetaPilotHullSet (q : Real) :
    Set (PaperThetaPilotPoint (l := l)) :=
  (paperThetaPilotHull (l := l) q : Set (PaperThetaPilotPoint (l := l)))

/-- The actual Haar volume of the paper hull. -/
noncomputable def paperThetaPilotHullVolume (q : Real) : ENNReal :=
  paperThetaPilotHaar (l := l) (paperThetaPilotHullSet (l := l) q)

/-- The actual real log-volume of the paper hull. -/
noncomputable def paperThetaPilotHullLogVolume (q : Real) : Real :=
  Real.log (paperThetaPilotHullVolume (l := l) q).toReal

/-- Actual volume of the hull at a bad place b. -/
noncomputable def paperBadThetaPilotHullVolume
    (b : Bad (nativePlaceSelection T)) : ENNReal :=
  paperThetaPilotHullVolume (l := l) (paperBaseQReal T b)

/-- Actual log-volume of the hull at a bad place b. -/
noncomputable def paperBadThetaPilotHullLogVolume
    (b : Bad (nativePlaceSelection T)) : Real :=
  paperThetaPilotHullLogVolume (l := l) (paperBaseQReal T b)

/-- Exact missing normalization data: a mono-analytic unit region, its
normalization, and compactness of the actual paper hull.  These are not
supplied by the raw Haar measure above. -/
structure PaperThetaPilotHullNormalizationData where
  unitRegion : Set (PaperThetaPilotPoint (l := l))
  unitRegion_normalized : Prop
  hull_compact : Prop
  monoAnalytic_compat : Prop

/-- The exact missing normalization proposition; no inhabitant is asserted. -/
def PaperThetaPilotHullNormalizationRequired : Prop :=
  Nonempty (PaperThetaPilotHullNormalizationData (l := l))

end LeanFormal.IUT.XiFPaper.PaperThetaPilotHullLogVolumeActual

end
