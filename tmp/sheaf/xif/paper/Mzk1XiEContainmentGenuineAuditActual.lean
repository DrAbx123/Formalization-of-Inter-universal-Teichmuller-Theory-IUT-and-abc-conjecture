/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.Mzk1QPilotSHEDoubleImageActual
import tmp.sheaf.xif.paper.PaperRootExtensionNormBoundActual
import tmp.sheaf.xif.paper.S664RootQUnitNormLeOneActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import Mathlib.Tactic

/-! A531: xi-e containment audit: definitional possibleRegion vs genuine objects.

(1) Vacuity.  If the 'q region' is `reg x` for the same `reg` producing the hull
possible images, the containment is the definitional green lemma
`MRRep.reg_subset_possibleRegion`; it holds for every raw output and representative
with no hypotheses (`definitional_containment_is_free` below), hence is NOT 3.12
evidence.  This is the trap of the A519/A521 possibleRegion route.

(2) Genuine objects (paper: q-pilot at (1,0), Theta possible images at (0,0)):
* Theta side: `thetaPilotImage T : ThetaLabel -> S1902Carrier T` (actual theta
  values root_b^{j^2}) and the coordinatewise hull `s1902Hull T`;
* q side: `qPilotCompletionImage T` in the DIFFERENT completion carrier
  `LiteralCompletionIQCarrier T` (S1929/QPilotSHEDoubleImage);
* the SHE arrow (green) gives `completionToRootExtension T qPilot =
  (thetaPilotImage label 1)^(2l)`; `thetaPilot_not_in_completionRange` shows the
  theta image is not a completion image (S342), so no definitional identification.

(3) Genuine containment PROVED below: the transported q-pilot image
`qPilotTransported T = completionToRootExtension T (qPilotCompletionImage T)` lies in
`s1902Hull T`.  Proof: SHE root relation, norm bound (RootQUnitNormLeOne), and the
hull radius being at least the label-1 theta norm.  No possibleRegion is involved.

(4) From the genuine containment and a monotone log-volume functional, the signed
paper inequality follows.  The identification of the readouts with -|log q| and
-|log Theta| is an explicit named field of `GenuineXiEData`, not a set equality. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentGenuineAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionNormBoundActual
open LeanFormal.IUT.XiFPaper.S664RootQUnitNormLeOneActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open Iut.Multiradial
open scoped Pointwise BigOperators

universe uG vG wG

/-! ## 1. Definitional vacuity -/

section Vacuity

variable {G : Type uG} [Groupoid.{vG} G] {A : Type wG} [Group A]

/-- The possibleRegion containment is definitional: it holds for every raw output,
region construction and representative, with no hypotheses.  Marker theorem: it
CANNOT be used as 3.12 evidence. -/
theorem definitional_containment_is_free
    (raw : RawOutput.{uG, vG, wG} G A) {P : G} {X : Type*}
    (reg : raw.F.obj P -> Set X) (x : raw.F.obj P) :
    reg x <= MRRep.possibleRegion (R := raw) reg (MRRep.mk (R := raw) x) :=
  MRRep.reg_subset_possibleRegion reg x

end Vacuity

/-! ## 2. Genuine objects and the proved containment -/

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The transported q-pilot image in the root-extension product carrier (SHE side). -/
noncomputable def qPilotTransported : S1902Carrier T :=
  completionToRootExtension T (qPilotCompletionImage T)

theorem qPilotTransported_apply (b : Bad (nativePlaceSelection T)) :
    qPilotTransported T b =
      (thetaPilotImage T (oneThetaLabel l) b) ^ (2 * l.value) := by
  unfold qPilotTransported
  exact she_arrow_apply T b

theorem qPilotTransported_norm_le_one (b : Bad (nativePlaceSelection T)) :
    ‖qPilotTransported T b‖ <= 1 := by
  rw [qPilotTransported_apply, norm_pow]
  have hbase : ‖thetaPilotImage T (oneThetaLabel l) b‖ <= 1 := by
    rw [thetaPilotImage_one_apply]
    exact rootNormedElement_norm_le_one (T := T) (b := b) (rootQUnitNormLeOne (T := T))
  exact pow_le_one₀ (norm_nonneg _) hbase

theorem thetaImage_one_norm_le_radius (b : Bad (nativePlaceSelection T)) :
    ‖thetaPilotImage T (oneThetaLabel l) b‖ <=
      (rootImageRadius T b : Real) := by
  rw [thetaPilotImage_one_apply]
  exact rootImageRadius_ge (T := T) (b := b) (oneThetaLabel l)

/-- **Genuine xi-e containment (PROVED)**: the transported q-pilot image lies in the
actual Theta-pilot hull.  No possibleRegion, no definitional containment. -/
theorem qPilotTransported_mem_hull : qPilotTransported T ∈ s1902Hull T := by
  rw [s1902Hull, rootExtensionProductImageHull, Set.mem_pi]
  intro b _
  rw [Metric.mem_closedBall, dist_eq_norm, qPilotTransported_apply, norm_pow]
  have hbase_le : ‖thetaPilotImage T (oneThetaLabel l) b‖ <=
      (rootImageRadius T b : Real) := thetaImage_one_norm_le_radius T b
  have hbase1 : ‖thetaPilotImage T (oneThetaLabel l) b‖ <= 1 := by
    rw [thetaPilotImage_one_apply]
    exact rootNormedElement_norm_le_one (T := T) (b := b) (rootQUnitNormLeOne (T := T))
  have h2l : 1 <= 2 * l.value :=
    Nat.succ_le_of_lt (Nat.mul_pos (by norm_num) l.prime.pos)
  have hdec : ‖thetaPilotImage T (oneThetaLabel l) b‖ ^ (2 * l.value) <=
      ‖thetaPilotImage T (oneThetaLabel l) b‖ ^ (1 : Nat) :=
    pow_le_pow_of_le_one (norm_nonneg _) hbase1 h2l
  calc ‖thetaPilotImage T (oneThetaLabel l) b‖ ^ (2 * l.value)
      <= ‖thetaPilotImage T (oneThetaLabel l) b‖ ^ (1 : Nat) := hdec
    _ = ‖thetaPilotImage T (oneThetaLabel l) b‖ := pow_one _
    _ <= (rootImageRadius T b : Real) := hbase_le

/-! ## 3. Signed comparison from the genuine containment -/

/-- Genuine xi-e data: a monotone increasing log-volume on theta-carrier regions
(IUT III Prop 3.9(i) packet/procession normalization is monotone: integral = 0 and
multiplication by p adds -log p) and the two DIFFERENT signed readings, with the
multiradial/1-column identifications recorded as explicit fields. -/
structure GenuineXiEData where
  muLog : Set (S1902Carrier T) -> Real
  muLog_mono : forall {S U : Set (S1902Carrier T)}, S <= U -> muLog S <= muLog U
  qSigned : Real
  thetaSigned : Real
  qSigned_eq : qSigned = muLog {qPilotTransported T}
  thetaSigned_eq : thetaSigned = muLog (s1902Hull T)

/-- **Paper signed inequality from genuine xi-e containment**: qSigned <= thetaSigned. -/
theorem genuine_signed_inequality (D : GenuineXiEData T) :
    D.qSigned <= D.thetaSigned := by
  rw [D.qSigned_eq, D.thetaSigned_eq]
  apply D.muLog_mono
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  exact qPilotTransported_mem_hull T

/-- Paper form: identifying the signed readings with the S3137 q-pilot reading
`-|log q|` and the actual Theta hull reading gives the Cor 3.12 inequality
`qPilotLogVolumeReading P <= thetaPilotHullLogVolumeReal C3`. -/
theorem genuine_cor312_inequality {V : Type} {I : OriginalInput l V}
    (D : GenuineXiEData T) (P : PaperQPilotObjectActual (l := l) (I := I))
    (qRead : D.qSigned = qPilotLogVolumeReading P)
    (thetaRead : D.thetaSigned = thetaPilotHullLogVolumeReal (C3 := ?_)) :
    qPilotLogVolumeReading P <= thetaPilotHullLogVolumeReal (C3 := ?_) :=
  by
  rw [← qRead, ← thetaRead]
  exact genuine_signed_inequality T D

end LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentGenuineAuditActual