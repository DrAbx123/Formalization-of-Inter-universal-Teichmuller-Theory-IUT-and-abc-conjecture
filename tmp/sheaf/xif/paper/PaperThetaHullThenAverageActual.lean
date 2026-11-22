import tmp.sheaf.xif.paper.PaperThetaPilotCarrierActual
import tmp.sheaf.xif.paper.PaperThetaPilotHullLogVolumeActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual
import tmp.sheaf.xif.paper.PaperWeightedThetaSignedActual
import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv

/-! # Paper Theta-pilot hull-then-average correction object

The 2.5 coefficient of PaperWeightedThetaSignedActual is average-first: it
averages the theta logarithms over F_l^x and only then applies the V_bad
weights.  The paper's -|log Theta| is hull-first: for each procession label j,
form the holomorphic hull of the possible images, take its actual log-volume,
and only then average over j in F_l^x.

This file constructs the actual hull-then-average candidate on the F_l^x-indexed
paper value carrier:

* paperLabelImage q j: the singleton possible-image point at label j;
* paperLabelHull q j: its actual generic holomorphic hull;
* paperLabelHullLogVolume q j: the actual Haar log-volume of that hull;
* paperHullThenAverage q: the final F_l^x procession average of those hull
  log-volumes.

It also records the distinct average-first theta-log scalar.  No equality
between the two orders is asserted, and no inequality is asserted.

No sorry, axiom, True, or PUnit is used. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperThetaHullThenAverageActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.PaperThetaPilotCarrierActual
open LeanFormal.IUT.XiFPaper.PaperThetaPilotHullLogVolumeActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.PaperWeightedThetaSignedActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (q : Real)

/-- Actual possible-image singleton at one F_l^x procession label. -/
noncomputable def paperLabelImage (j : ProcessionLabel l) :
    Set (PaperThetaPilotPoint (l := l)) :=
  {paperThetaPilotPointAt (l := l) q j}

/-- Actual holomorphic hull of the possible-image singleton at one label. -/
noncomputable def paperLabelHull (j : ProcessionLabel l) :
    Submonoid (PaperThetaPilotPoint (l := l)) :=
  holomorphicHull (paperScalingUnits (l := l))
    (paperLabelImage (l := l) q j)

/-- Actual Haar log-volume of the per-label hull. -/
noncomputable def paperLabelHullLogVolume (j : ProcessionLabel l) : Real :=
  Real.log
    (paperThetaPilotHaar (l := l)
      (paperLabelHull (l := l) q j : Set (PaperThetaPilotPoint (l := l)))).toReal

/-- Hull-then-average paper candidate: first the actual per-label hull
log-volumes, then the F_l^x procession average. -/
noncomputable def paperHullThenAverage : Real :=
  (Fintype.card (ProcessionLabel l) : Real)⁻¹ *
    ∑ j : ProcessionLabel l, paperLabelHullLogVolume (l := l) q j

/-- Average-first theta-log scalar: the old 2.5 coefficient object's structural
form, averaging ordinary theta logarithms over F_l^x. -/
noncomputable def paperAverageFirstThetaLog : Real :=
  (Fintype.card (ProcessionLabel l) : Real)⁻¹ *
    ∑ j : ProcessionLabel l,
      Real.log
        (paperThetaValue (l := l) q
          (SignedLabel.representative l.value (j : ZMod l.value)))

/-- Actual hull-then-average data package. -/
structure PaperHullThenAverageData where
  labelImage : ProcessionLabel l -> Set (PaperThetaPilotPoint (l := l))
  labelImage_eq : labelImage = paperLabelImage (l := l) q
  labelHull : ProcessionLabel l -> Submonoid (PaperThetaPilotPoint (l := l))
  labelHull_eq : labelHull = paperLabelHull (l := l) q
  labelLogVolume : ProcessionLabel l -> Real
  labelLogVolume_eq : labelLogVolume = paperLabelHullLogVolume (l := l) q
  average : Real
  average_eq : average = paperHullThenAverage (l := l) q

/-- The actual hull-then-average data. -/
noncomputable def paperHullThenAverageData :
    PaperHullThenAverageData (l := l) q where
  labelImage := paperLabelImage (l := l) q
  labelImage_eq := rfl
  labelHull := paperLabelHull (l := l) q
  labelHull_eq := rfl
  labelLogVolume := paperLabelHullLogVolume (l := l) q
  labelLogVolume_eq := rfl
  average := paperHullThenAverage (l := l) q
  average_eq := rfl

/-- The hull-then-average definition unfolds to the per-label hull-volume
average, not to an average of theta logarithms. -/
theorem paperHullThenAverage_eq :
    paperHullThenAverage (l := l) q =
      (Fintype.card (ProcessionLabel l) : Real)⁻¹ *
        ∑ j : ProcessionLabel l,
          Real.log
            (paperThetaPilotHaar (l := l)
              (paperLabelHull (l := l) q j :
                Set (PaperThetaPilotPoint (l := l)))).toReal := rfl

/-- Exact order-distinction target: the paper quantity requires hull before
average, while the 2.5 coefficient is average before (or without) hull. -/
def PaperHullBeforeAverageRequired : Prop :=
  paperHullThenAverage (l := l) q =
    (Fintype.card (ProcessionLabel l) : Real)⁻¹ *
      ∑ j : ProcessionLabel l, paperLabelHullLogVolume (l := l) q j

theorem paperHullBeforeAverageRequired_holds :
    PaperHullBeforeAverageRequired (l := l) q := rfl

end LeanFormal.IUT.XiFPaper.PaperThetaHullThenAverageActual

end
