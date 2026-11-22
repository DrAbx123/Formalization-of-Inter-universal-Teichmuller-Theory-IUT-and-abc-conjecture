/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import tmp.sheaf.xif.paper.Mzk1MonotoneGogopexBridgeActual
import tmp.sheaf.xif.paper.Mzk1LogVolumeMonotoneActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentMonotoneActual
import tmp.sheaf.xif.paper.Mzk1MonotoneSignedDirectionActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import Mathlib.Tactic

/-! A524: signed assembly for Cor 3.12: qRegion ⊆ hull + signed log-volume
   => signed Corollary 3.12 inequality, on the actual C3 container.

Assembles:
* `Mzk1MonotoneGogopexBridgeActual` (signed log-volume, containment ==> signed
  Gogopex inequality, positive-magnitude obstruction);
* `Mzk1XiEContainmentMonotoneActual` (actual C3: qRegion = actual tensor region,
  thetaPilotHull = actualRegion, Haar log-volume monotonicity);
* `Mzk1LogVolumeMonotoneActual` (container-level possibleRegion -> hullAdmissible
  membership, packetVol/globalVol/processionVol monotonicity);
* `Mzk1MonotoneSignedDirectionActual` (direction audit, magnitude obstruction).

Measure prerequisites are explicit everywhere: the q region has positive Haar
measure; the hull has finite Haar measure (proved from compactness in S3137). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1SignedAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentMonotoneActual
open LeanFormal.IUT.XiFPaper.Mzk1LogVolumeMonotoneActual
open LeanFormal.IUT.Objects.MonotoneGogopexBridge
open MeasureTheory
open scoped Pointwise ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance signedAssemblyBlockMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance signedAssemblyBlockBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-! ## 1. qRegion ⊆ Theta hull on the actual C3 container -/

theorem qPilotRegion_subset_hull :
    (qPilotContainerRegion C3 : Set (C3LogShellTensorBlock C3)) <=
      thetaPilotHull C3 :=
  (thetaPilotHull_eq_qPilotRegion C3).ge

/-! ## 2. Signed log-volume inequality (the paper direction) -/

/-- The actual signed Haar log-volume of a region (same function as the bridge's
`signedLogVolume` and the XiE file's `haarLogVolume`). -/
def signedHaarLogVolume (S : Set (C3LogShellTensorBlock C3)) : Real :=
  signedLogVolume (actualC3LogShellTensorHaar C3) S

theorem signedHaarLogVolume_eq (S : Set (C3LogShellTensorBlock C3)) :
    signedHaarLogVolume C3 S =
      Real.log ((actualC3LogShellTensorHaar C3) S).toReal := rfl

/-- **Region-level signed inequality** on the actual C3 data.  Since S3137 proves
`thetaPilotHull = actualC3LogShellTensorRegion`, this is a same-region identity
(equality), so it is NOT the paper q-pilot/Theta-pilot comparison; the paper
comparison is `PaperReadingComparison`. -/
theorem signed_qRegion_le_hull
    (hqpos : 0 < (actualC3LogShellTensorHaar C3) (qPilotContainerRegion C3)) :
    signedHaarLogVolume C3 (qPilotContainerRegion C3) <=
      signedHaarLogVolume C3 (thetaPilotHull C3) := by
  unfold signedHaarLogVolume
  exact signedLogVolume_mono (actualC3LogShellTensorHaar C3)
    (qPilotRegion_subset_hull C3) hqpos (thetaPilotHull_measure_lt_top (C3 := C3)).ne

/-! ## 3. Gogopex signed Corollary 3.12 -/

/-- Region-level Gogopex `Corollary312Inequality`: same-region identity, NOT the paper
q-pilot/Theta-pilot comparison (see `PaperReadingComparison`). -/
theorem signed_corollary312
    (hqpos : 0 < (actualC3LogShellTensorHaar C3) (qPilotContainerRegion C3)) :
    Iut.Stage1.Corollary312Inequality
      { side := Iut.Stage1.PilotSide.theta,
        value := signedHaarLogVolume C3 (thetaPilotHull C3) }
      { side := Iut.Stage1.PilotSide.q,
        value := signedHaarLogVolume C3 (qPilotContainerRegion C3) } := by
  unfold Iut.Stage1.Corollary312Inequality
  have h := signed_qRegion_le_hull C3 hqpos
  linarith

/-- Reading form: if the signed q-reading is `-|log q|` and the signed hull reading
is `-|log Theta|`, the signed inequality is exactly paper Cor 3.12's
`-|log q| <= -|log Theta|`. -/
theorem signed_readings_are_paper_readings {signedQ signedH A B : Real}
    (hQ : signedQ = -A) (hH : signedH = -B) (hineq : signedQ <= signedH) :
    -A <= -B := by
  rwa [hQ, hH] at hineq

/-- C3 instantiation of the reading identification: if the actual q region signed
reading and the actual hull signed reading are the paper readings, the signed C3
inequality yields `-|log q| <= -|log Theta|`. -/
theorem signed_c3_paper_form
    (hqpos : 0 < (actualC3LogShellTensorHaar C3) (qPilotContainerRegion C3))
    (A B : Real)
    (hQ : signedHaarLogVolume C3 (qPilotContainerRegion C3) = -A)
    (hH : signedHaarLogVolume C3 (thetaPilotHull C3) = -B) :
    -A <= -B :=
  signed_readings_are_paper_readings hQ hH (signed_qRegion_le_hull C3 hqpos)

theorem c3_thetaPilotHullLogVolume_eq_signed :
    thetaPilotHullLogVolumeReal C3 =
      signedHaarLogVolume C3 (thetaPilotHull C3) :=
  rfl

/-! ## 3b. Paper readings (different objects) and the named comparison -/

/-- The two paper signed readings: the S3137 q-pilot reading `-|log q|` and the actual
Theta-pilot hull Haar reading.  These are DIFFERENT objects (no region renaming). -/
structure PaperReadings (P : PaperQPilotObjectActual (l := l) (I := I)) where
  qSigned : Real
  qSigned_eq : qSigned = qPilotLogVolumeReading P
  thetaSigned : Real
  thetaSigned_eq : thetaSigned = thetaPilotHullLogVolumeReal C3
  qSigned_neg : qSigned < 0

noncomputable def paperReadings (P : PaperQPilotObjectActual (l := l) (I := I)) :
    PaperReadings C3 P where
  qSigned := qPilotLogVolumeReading P
  qSigned_eq := rfl
  thetaSigned := thetaPilotHullLogVolumeReal C3
  thetaSigned_eq := rfl
  qSigned_neg := P.signedQPilotLogVolume_neg

/-- The paper 3.12 comparison of the two different readings: named candidate. -/
def PaperReadingComparison {P : PaperQPilotObjectActual (l := l) (I := I)}
    (D : PaperReadings C3 P) : Prop :=
  D.qSigned <= D.thetaSigned

theorem paperReadingComparison_iff {P : PaperQPilotObjectActual (l := l) (I := I)}
    (D : PaperReadings C3 P) :
    PaperReadingComparison C3 D <->
      qPilotLogVolumeReading P <= thetaPilotHullLogVolumeReal C3 := by
  unfold PaperReadingComparison
  rw [D.qSigned_eq, D.thetaSigned_eq]

theorem paperReadingComparison_iff_s3137_named
    {P : PaperQPilotObjectActual (l := l) (I := I)} (D : PaperReadings C3 P) :
    PaperReadingComparison C3 D <-> qThetaPilotLogVolumeComparison C3 P := by
  rw [paperReadingComparison_iff, qThetaPilotLogVolumeComparison_iff]

/-- Gogopex signed Cor 3.12 from the NAMED paper comparison (conditional assembly).
The Gogopex inequality uses the MAGNITUDES, i.e. the negated signed readings:
`-theta >= -q` with theta := -D.thetaSigned, q := -D.qSigned is equivalent to
`D.qSigned <= D.thetaSigned`, i.e. the paper comparison. -/
theorem paper_signed_corollary312_of_candidate
    {P : PaperQPilotObjectActual (l := l) (I := I)} (D : PaperReadings C3 P)
    (hcomp : PaperReadingComparison C3 D) :
    Iut.Stage1.Corollary312Inequality
      { side := Iut.Stage1.PilotSide.theta, value := -D.thetaSigned }
      { side := Iut.Stage1.PilotSide.q, value := -D.qSigned } := by
  unfold Iut.Stage1.Corollary312Inequality PaperReadingComparison at *
  linarith

/-! ## 4. Container-level assembly: possibleRegion ⊆ hullAdmissible and volumes -/

universe u₁ u₂ v uG vG wG

theorem possibleRegion_subset_hullAdmissible
    {D : Iut.LargeVolumeContainerData.{u₁, u₂, v} Iut.RationalPlace Unit}
    (H : Iut.ContainerHullSystem D) {i : Fin D.proc.length}
    {R : D.AdmissibleRegion i} (hR : H.IsAdmissible R) (vQ : Iut.RationalPlace)
    {S : Set (D.packet i vQ).Total} (hSR : S <= R.region vQ) :
    S <= (H.hullAdmissible R).region vQ :=
  possibleImage_subset_hullAdmissible H hR vQ hSR

theorem globalVol_mono_of_hullAdmissible
    {D : Iut.LargeVolumeContainerData.{u₁, u₂, v} Iut.RationalPlace Unit}
    (vol : Iut.LogVolumeData D) (hmono : PacketVolMonotone vol)
    (H : Iut.ContainerHullSystem D) {i : Fin D.proc.length}
    {R : D.AdmissibleRegion i} (hR : H.IsAdmissible R) :
    vol.globalVol R <= vol.globalVol (H.hullAdmissible R) :=
  globalVol_mono vol hmono (H.le_hullAdmissible hR)

theorem processionVol_mono_of_hullFamily
    {D : Iut.LargeVolumeContainerData.{u₁, u₂, v} Iut.RationalPlace Unit}
    (vol : Iut.LogVolumeData D) (hmono : PacketVolMonotone vol)
    (hlen : 0 < D.proc.length) (H : Iut.ContainerHullSystem D)
    {R : forall i : Fin D.proc.length, D.AdmissibleRegion i}
    (hR : forall i, H.IsAdmissible (R i)) :
    vol.processionVol R <= vol.processionVol (H.hullFamily R) :=
  processionVol_mono vol hmono hlen (fun i => H.le_hullAdmissible (hR i))

end LeanFormal.IUT.XiFPaper.Mzk1SignedAssemblyActual