import tmp.sheaf.xif.paper.S3138SourceProcessionCarrierActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceInternalWiring
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3138: bridge from the Theorem 3.11 internal wiring to the source Step XI input

This file connects the source-level Step XI input of
`S3138SourceProcessionCarrierActual` (built from a genuine `OriginalInput`) to
the *realization* side of Theorem 3.11, through a supplied
`SourceInternalWiring` record (`Theorem311/SourceInternalWiring.lean`): the
H1/H2 to realization alignment `SourceH1H2Alignment`, the canonical K1 vertical
boundary, and the K2 Frobenioid boundary.

What is identified here (all actual, no new data):

* the aligned realization Hodge index of a source lattice point `(n,m)`:
  `alignedSourceIndex` = `choiceHodgeIndex (choiceFamilyIndex.symm (indexOf n m))`;
* the source Step XI `target_q` (the actual terminal theater Theta q) is the
  realization Hodge q-parameter at the aligned index (`A.q_at`);
* the source base packet log-volume is the sum of the logs of the realization
  Hodge scale data at the aligned index (`A.scale_at`), i.e. the realization
  readout of the same Theta profile;
* the source boundary's alignment family indices are the actual
  `choiceFamilyIndex` data (`A.choice_index_at`).

The supplied wiring record and its alignment/K2 fields remain explicit
source-facing data; this file only transports the already-proved alignment
laws to the Step XI boundary objects.

Source: IUT III, Theorem 3.11 (opening/H1-H2, K1/K2); consumer: the Step XI
V1/V2 boundary files of this stream.
-/

namespace LeanFormal.IUT.XiFPaper.S3138SourceInternalWiringStepXIActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.SourceProcessionBoundary
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionProfileActual
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCarrierActual

universe u uv upi umon ui v w ux uy

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{u, uv, upi, umon, ui} l V}
variable {R : SourceTheorem311Realization.{u, v, w} l Label Choice}
variable {P : H2SpokePermutation I}
variable {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
variable (W : SourceInternalWiring I R P X Y)

/-- The realization Hodge index aligned with the source lattice point
`(n,m)` under the supplied H1/H2 alignment. -/
noncomputable def alignedSourceIndex (n m : Int) : R.procession.hodge.index :=
  W.alignment.choiceHodgeIndex
    (W.alignment.choiceFamilyIndex.symm (I.indexOf n m))

/-- The aligned index decodes to the source family index of `(n,m)`. -/
theorem alignedSourceIndex_hodgeIndex (n m : Int) :
    W.alignment.hodgeIndex (alignedSourceIndex W n m) = I.indexOf n m := by
  unfold alignedSourceIndex
  rw [W.alignment.choice_index_at, Equiv.apply_symm_apply]

/-- The aligned index has the actual family index of the source theater. -/
theorem alignedSourceIndex_familyIndex (n m : Int) :
    W.alignment.choiceFamilyIndex
        (W.alignment.choiceFamilyIndex.symm (I.indexOf n m)) = I.indexOf n m :=
  Equiv.apply_symm_apply W.alignment.choiceFamilyIndex (I.indexOf n m)

/-- The source Step XI target q is the realization Hodge q-parameter at the
aligned index: the actual terminal theater Theta q is read out of the
realization's Hodge system. -/
theorem sourceStepXIInput_target_q_eq_hodge_q (n m : Int) :
    (sourceStepXIInput I n m).target_q =
      R.procession.hodge.qParameter (alignedSourceIndex W n m) := by
  show (I.theaterAt n m).thetaPacket.q =
    R.procession.hodge.qParameter (alignedSourceIndex W n m)
  rw [W.alignment.q_at (alignedSourceIndex W n m),
    alignedSourceIndex_hodgeIndex W n m]
  rfl

/-- The source base packet log-volume is the realization readout of the Theta
profile: the sum of the logs of the aligned Hodge scale data. -/
theorem sourceStepXIInput_base_volume_eq_hodge_scale_sum (n m : Int) :
    (sourceStepXIInput I n m).packetVolume (SourceStepXIBase I) =
      ∑ j : SignedLabel l.value,
        Real.log (R.procession.hodge.scale (alignedSourceIndex W 0 0) j) := by
  show (I.theaterAt 0 0).thetaPacket.logVolume = _
  rw [FiniteThetaPacket.logVolume_eq_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [W.alignment.scale_at (alignedSourceIndex W 0 0) j,
    alignedSourceIndex_hodgeIndex W 0 0]
  rfl

/-- The source boundary's theater q equals the realization Hodge q at the
aligned index (target q identification in source-stepXI target form). -/
theorem sourceStepXIInput_theater_q_eq_hodge_q (n m : Int) :
    (I.theaterAt n m).thetaPacket.q =
      R.procession.hodge.qParameter (alignedSourceIndex W n m) :=
  sourceStepXIInput_target_q_eq_hodge_q W n m

end LeanFormal.IUT.XiFPaper.S3138SourceInternalWiringStepXIActual

end
