/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1KummerRealizationActual

/-!
# A544 consumer of the PROVED Kummer realization (green chain)

Consumers of the now-green `Mzk1KummerTransportActual`/`Mzk1KummerRealizationActual`:
* the q-pilot image in the theta carrier is the Kummer (`2l`-power) image of the
  label-1 Theta image (`qImage_realized` is a THEOREM, not a named field);
* the realized q image lies in the actual `s1902Hull` (`qImage_realized_mem_hull`);
* paper readings: STRICT signed inequality `qReading < thetaReading` and the
  `C_Theta >= -1` form `thetaReading <= C * (-qReading) -> -1 <= C`.

No definitional possibleRegion is used; the containment is the proved Kummer/norm-bound
statement.  The only named inputs remain the PaperKummerReading realization equalities
and the strict volume increase.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- **The proved Kummer realization bundle**: the q-pilot image is the Kummer image of
  the Theta image, and it lies in the actual Theta hull. -/
theorem kummerRealizationBundle :
    (genuineKummerData T).qImageInTheta =
        kummerMap T (genuineKummerData T).thetaImage ∧
      (genuineKummerData T).qImageInTheta ∈ s1902Hull T :=
  ⟨qImage_realized T,
   by simpa [genuineKummerData] using qImage_realized_mem_hull T⟩

/-- The theta image of the genuine data is the label-1 theta image (re-export). -/
theorem thetaImage_eq_thetaOne :
    (genuineKummerData T).thetaImage = thetaOneCarrier T :=
  thetaImage_realized T

/-- The Kummer realization in power form (re-export): the q image is `theta^(2l)`. -/
theorem kummerRealization_power :
    kummerMap T (thetaOneCarrier T) = qPilotInThetaCarrier T :=
  kummerMap_thetaOne T

/-- **The paper strict reading**: `qReading < thetaReading`. -/
theorem paperReading_strict (R : PaperKummerReading T) :
    R.qReading < R.thetaReading :=
  paperKummerReading_strict T R

/-- **The paper `C_Theta >= -1` form** for the realized readings. -/
theorem paperReading_CTheta (R : PaperKummerReading T) (hqneg : R.qReading < 0)
    {C : ℝ} (hC : R.thetaReading ≤ C * (-R.qReading)) : -1 ≤ C := by
  have hqpos : 0 < -R.qReading := neg_pos.mpr hqneg
  have h1 : R.qReading < C * (-R.qReading) :=
    lt_of_lt_of_le (paperKummerReading_strict T R) hC
  have h2 : R.qReading / (-R.qReading) < C := (div_lt_iff₀ hqpos).mpr h1
  have h3 : R.qReading / (-R.qReading) = -1 := by
    have hne : R.qReading ≠ 0 := ne_of_lt hqneg
    calc R.qReading / (-R.qReading) = -(R.qReading / R.qReading) := by rw [div_neg]
      _ = -(1 : ℝ) := by rw [div_self hne]
      _ = -1 := by ring
  rw [h3] at h2
  linarith

end

end LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationConsumerActual