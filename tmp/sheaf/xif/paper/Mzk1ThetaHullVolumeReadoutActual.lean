/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual
import tmp.sheaf.xif.paper.S201RootThetaNormLActual
import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual
import tmp.sheaf.xif.paper.Mzk1HullReadoutReuseActual
import Mathlib.Tactic

/-! A518: Theta-pilot hull volume readout object.
Objects and real lemmas (no comparison):
* thetaPilotLogVolumeReadout = S3137 actual hull Haar log-volume;
  constructed equalities to the hull Haar and to the actual C3 region;
* p-scaling of the readout (Prop 3.9 (i) at the actual hull);
* the local j^2 Theta scaling in the form gaussExponent/(2l) * log q
  from the actual S201 root norms (laichunwing 07);
* the possible-log-volume set R_{<= theta} as an (Ind3) region, and the
  multiradial possibleRegion inclusion of a representative region
  (LANA Multiradial Spec, green Ref copy). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaHullVolumeReadoutActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.Mzk1HullReadoutReuseActual
open Iut.Multiradial
open MeasureTheory
open scoped BigOperators

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-! ## 1. The Theta-pilot hull volume readout -/

/-- The Theta-pilot hull volume readout: the actual S3137 Haar log-volume of the
actual Theta-pilot hull. -/
noncomputable def thetaPilotLogVolumeReadout : Real :=
  thetaPilotHullLogVolumeReal C3

theorem thetaPilotLogVolumeReadout_constructed :
    thetaPilotLogVolumeReadout C3 = thetaPilotHullLogVolumeReal C3 := rfl

theorem thetaPilotLogVolumeReadout_eq_hullHaar :
    thetaPilotLogVolumeReadout C3 =
      Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal :=
  thetaPilotHullLogVolumeReal_eq_regionLogVolume (C3 := C3)

theorem thetaPilotLogVolumeReadout_eq_actualRegion :
    thetaPilotLogVolumeReadout C3 =
      Real.log ((actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3)).toReal :=
  thetaPilotHullLogVolumeReal_eq_actualRegion (C3 := C3)

theorem thetaPilotLogVolumeReadout_eq_reuse :
    thetaPilotLogVolumeReadout C3 =
      Mzk1HullReadoutReuseActual.thetaHullReadout C3 := rfl

theorem thetaPilotLogVolumeReadout_measure_lt_top :
    (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤ :=
  thetaPilotHull_measure_lt_top (C3 := C3)

/-- p-scaling of the hull volume readout: multiplying the actual hull by p shifts
the Haar log-volume by -[block : Q_p] * log p (IUT III, Prop 3.9 (i)). -/
theorem thetaPilotLogVolumeReadout_p_smul
    (hpos : 0 < (actualC3LogShellTensorHaar C3) (thetaPilotHull C3)) :
    Real.log ((actualC3LogShellTensorHaar C3)
        ((C3.p : ℚ_[C3.p]) • thetaPilotHull C3)).toReal =
      -(c3TensorBlockDimension C3 : Real) * Real.log (C3.p : Real) +
        thetaPilotLogVolumeReadout C3 :=
  thetaPilotHull_log_measure_prime_smul (C3 := C3) hpos

/-! ## 2. Local j^2 Theta scaling against the actual q log -/

variable {T : SourceNativeInitialThetaData.{0} l}
variable (b : Bad (nativePlaceSelection T))

theorem twoL_mul_rootLog_eq_localQLog :
    (2 * (l.value : Real)) * Real.log (rootNormedElementNorm T b) =
      Real.log ‖(sourceRootQUnit T b : rootBase T b)‖ := by
  have h := congrArg Real.log (rootNormedElementNorm_pow_twoL T b)
  rw [Real.log_pow] at h
  simpa [rootNormedElementNorm, Nat.cast_mul] using h

/-- Local Theta log scaling: log ||Theta_j|| = (j^2/(2l)) * log q (laichunwing
07 / Joshi ATS III, realized on the actual S201 root norms). -/
theorem thetaLocalLog_eq_gaussExponent_div_twoL_mul :
    Real.log ‖(rootNormedThetaValueInL T b j : rootNormedExtension T b)‖ =
      (gaussExponent j.1 : Real) / (2 * (l.value : Real)) *
        Real.log ‖(sourceRootQUnit T b : rootBase T b)‖ := by
  rw [rootNormedThetaValueInL_norm, Real.log_zpow]
  have hlog := twoL_mul_rootLog_eq_localQLog (l := l) (T := T) b
  have hlpos : (0 : Real) < (l.value : Real) := by exact_mod_cast l.prime.pos
  have h2 : (2 * (l.value : Real)) ≠ 0 := by positivity
  have hroot : Real.log (rootNormedElementNorm T b) =
      Real.log ‖(sourceRootQUnit T b : rootBase T b)‖ / (2 * (l.value : Real)) := by
    rw [eq_div_iff h2]
    linarith [hlog]
  rw [hroot]
  field_simp [h2]
  ring

/-! ## 3. Possible Theta-pilot log-volumes as an (Ind3) region -/

/-- The paper's set R_{<= theta} of possible pilot log-volumes. -/
def possibleThetaLogVolumes (thetaHullLog : Real) : Set Real :=
  Set.Iic thetaHullLog

theorem possibleThetaLogVolumes_self_mem (thetaHullLog : Real) :
    possibleThetaLogVolumes thetaHullLog = Set.Iic thetaHullLog := rfl

/-- The hull region is upper-semi-compatible with itself, hence a possible
(Ind3) region. -/
theorem hullLogVolume_mem_ind3 (thetaHullLog : Real) :
    Set.Iic thetaHullLog ∈ Iut.Multiradial.ind3Possible (Set.Iic thetaHullLog) :=
  subset_rfl

/-- The union of the (Ind3) possible regions is the region itself. -/
theorem hullLogVolume_sUnion_ind3 (thetaHullLog : Real) :
    ⋃₀ Iut.Multiradial.ind3Possible (Set.Iic thetaHullLog) = Set.Iic thetaHullLog :=
  Iut.Multiradial.sUnion_ind3Possible (Set.Iic thetaHullLog)

/-! ## 4. Multiradial possibleRegion inclusion (LANA green copy) -/

universe u v w w'

variable {G : Type u} [Groupoid.{v} G] {A : Type w'} [Group A]

/-- A representative region of a possible Theta-pilot log-volume is contained in
the multiradial possible images (Thm 3.11(i); LANA possibleRegion). -/
theorem possibleLogVolume_subset_possibleRegion
    (raw : RawOutput.{u, v, w} G A) {P : G} (x : raw.F.obj P) (thetaHullLog : Real) :
    Set.Iic thetaHullLog <= MRRep.possibleRegion (R := raw)
      (fun _ => Set.Iic thetaHullLog) (MRRep.mk (R := raw) x) :=
  MRRep.reg_subset_possibleRegion (fun _ => Set.Iic thetaHullLog) x

/-! ## 5. The readout object -/

/-- The Theta-pilot hull volume readout object: hull, Haar log-volume, p-scaled
readout and the local j^2 scaling datum. -/
structure ThetaHullVolumeObject
    (C3 : SourcePilotRegionData (l := l) (V := V) I) where
  hull : Set (C3LogShellTensorBlock C3)
  hull_eq : hull = thetaPilotHull C3
  haarLogVolume : Real
  haarLogVolume_eq : haarLogVolume = thetaPilotLogVolumeReadout C3
  hullMeasureLtTop : (actualC3LogShellTensorHaar C3) hull < ⊤
  pScaledReadout : Real
  pScaledReadout_eq : pScaledReadout =
    -(c3TensorBlockDimension C3 : Real) * Real.log (C3.p : Real) +
      thetaPilotLogVolumeReadout C3

noncomputable def thetaHullVolumeObject :
    ThetaHullVolumeObject C3 where
  hull := thetaPilotHull C3
  hull_eq := rfl
  haarLogVolume := thetaPilotLogVolumeReadout C3
  haarLogVolume_eq := rfl
  hullMeasureLtTop := thetaPilotHull_measure_lt_top (C3 := C3)
  pScaledReadout := -(c3TensorBlockDimension C3 : Real) * Real.log (C3.p : Real) +
    thetaPilotLogVolumeReadout C3
  pScaledReadout_eq := rfl

theorem thetaHullVolumeObject_constructed :
    (thetaHullVolumeObject C3).hull = thetaPilotHull C3 ∧
    (thetaHullVolumeObject C3).haarLogVolume = thetaPilotLogVolumeReadout C3 := by
  refine ⟨rfl, rfl⟩

end LeanFormal.IUT.XiFPaper.Mzk1ThetaHullVolumeReadoutActual