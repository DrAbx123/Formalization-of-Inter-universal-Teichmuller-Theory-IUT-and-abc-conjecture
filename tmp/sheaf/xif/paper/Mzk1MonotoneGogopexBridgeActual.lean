/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual
import tmp.sheaf.xif.paper.Mzk1MonotoneSignedDirectionActual
import tmp.sheaf.gogopex.Iut.Stage1.PilotComparison
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import Mathlib.MeasureTheory.Measure.MeasureSpace

noncomputable section

/-!
# A524 monotone bridge: qRegion ⊆ hull with SIGNED log-volume

The geometric direction is `qRegion ⊆ possibleRegion ⊆ hull` (the hull is the
holomorphic hull of the possible images).  With the signed reading
`signedLogVolume mu S = Real.log ((mu S).toReal)` (negative on the actual
hull/q regions), measure monotonicity gives
`signedLogVolume mu qRegion ≤ signedLogVolume mu hull`, which is exactly the
paper Cor 3.12 inequality `-|log q| ≤ -|log Theta|`.  No `hull ⊆ qRegion`, no
positive-magnitude/negation hypothesis.  The old positive-magnitude reversal is
recorded as an obstruction. -/

namespace LeanFormal.IUT.Objects.MonotoneGogopexBridge

open CategoryTheory
open Iut Multiradial
open Iut.Stage1
open MeasureTheory
open LeanFormal.IUT.XiFPaper.Mzk1MonotoneSignedDirectionActual

universe u v w w'

variable {G : Type u} [Groupoid G] {A : Type w'} [Group A]

/-- General monotonicity of a real-valued log-volume under inclusion. -/
theorem logVolume_le_of_subset {X : Type*} (logVolume : Set X → ℝ)
    (mono : ∀ {S T : Set X}, S ⊆ T → logVolume S ≤ logVolume T)
    {S T : Set X} (h : S ⊆ T) : logVolume S ≤ logVolume T :=
  mono h

/-- `qRegion` of a representative is contained in any hull containing the whole
possible-image region (consumer of LANA `MRRep.reg_subset_possibleRegion`). -/
theorem qRegion_subset_hull {X : Type*} (R : RawOutput G A) {P : G}
    (reg : R.F.obj P → Set X) (x : R.F.obj P) {hull : Set X}
    (hHull : MRRep.possibleRegion (R := R) reg (MRRep.mk (R := R) x) ⊆ hull) :
    reg x ⊆ hull :=
  Set.Subset.trans (MRRep.reg_subset_possibleRegion (R := R) reg x) hHull

/-- Signed log-volume monotonicity: `qRegion ⊆ hull` gives the paper direction
`signedLogVolume qRegion ≤ signedLogVolume hull`.  The measure premises are
exactly nonzeroness of the q-region and finiteness of the hull. -/
theorem signedLogVolume_le_of_qRegion_subset_hull {X : Type*} [MeasurableSpace X]
    (mu : Measure X) {qRegion hull : Set X} (hsub : qRegion ⊆ hull)
    (hq : 0 < mu qRegion) (hh : mu hull ≠ ⊤) :
    signedLogVolume mu qRegion ≤ signedLogVolume mu hull :=
  signedLogVolume_mono mu hsub hq hh

/-- Gogopex `Corollary312Inequality` from the signed containment.  The tagged
values are the negated signed readings, i.e. the positive magnitudes; the
Gogopex inequality `-theta.value ≥ -q.value` is then exactly the signed
paper direction. -/
theorem gogopex_signedComparison_of_qRegion_subset_hull {X : Type*}
    [MeasurableSpace X] (mu : Measure X) {qRegion hull : Set X}
    (hsub : qRegion ⊆ hull) (hq : 0 < mu qRegion) (hh : mu hull ≠ ⊤) :
    Corollary312Inequality
      { side := PilotSide.theta, value := -signedLogVolume mu hull }
      { side := PilotSide.q, value := -signedLogVolume mu qRegion } := by
  unfold Corollary312Inequality
  have h := signedLogVolume_le_of_qRegion_subset_hull mu hsub hq hh
  linarith

/-- Positive-magnitude route obstruction: `qVol ≤ hVol` does not give the
reversed claimed inequality unless equality. -/
theorem positive_magnitude_direction_obstruction {qVol hVol : ℝ} (h : qVol ≤ hVol)
    (hlt : qVol < hVol) : ¬ (-hVol ≥ -qVol) := by
  intro hge
  linarith

/-- The StepXI contract with signed q/Theta readings and the containment inequality. -/
def contractOfSignedContainment {X : Type*} [MeasurableSpace X] (mu : Measure X)
    {qRegion hull : Set X} (hsub : qRegion ⊆ hull)
    (hqneg : signedLogVolume mu qRegion < 0)
    (hq : 0 < mu qRegion) (hh : mu hull ≠ ⊤) : StepXIContract where
  qSigned := signedLogVolume mu qRegion
  thetaSigned := signedLogVolume mu hull
  targetSigned := signedLogVolume mu hull
  q_negative := hqneg
  ipl := True
  she := True
  apt := True
  ipl_evidence := trivial
  she_evidence := trivial
  apt_evidence := trivial
  q_le_target := signedLogVolume_le_of_qRegion_subset_hull mu hsub hq hh
  target_le_theta := le_rfl

/-- Assembly of the paper signed inequality from `qRegion ⊆ hull`. -/
theorem cor312Conclusion_of_qRegion_subset_hull {X : Type*} [MeasurableSpace X]
    (mu : Measure X) {qRegion hull : Set X} (hsub : qRegion ⊆ hull)
    (hqneg : signedLogVolume mu qRegion < 0)
    (hq : 0 < mu qRegion) (hh : mu hull ≠ ⊤) :
    Cor312Conclusion (contractOfSignedContainment mu hsub hqneg hq hh) :=
  signedLogVolume_le_of_qRegion_subset_hull mu hsub hq hh

end LeanFormal.IUT.Objects.MonotoneGogopexBridge

end
