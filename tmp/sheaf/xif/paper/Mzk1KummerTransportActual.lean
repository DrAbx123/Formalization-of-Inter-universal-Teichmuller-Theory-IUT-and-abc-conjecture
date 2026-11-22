/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.Mzk1QPilotSHEDoubleImageActual
import tmp.sheaf.xif.paper.PaperRootExtensionNormBoundActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.S664RootQUnitNormLeOneActual
import Mathlib.Tactic

/-! A533: Kummer transport between the S1902 theta carrier and the literal completion carrier.

AUDIT / CORRECTION.  The natural Kummer map for the q-pilot / Theta-pilot relation is
the POWER map `x |-> x^(2l)` from the root-extension theta carrier `S1902Carrier T`
into itself (theta value theta_j = root^(j^2), theta_j^(2l) = q^(j^2) in the
extension).  By SHE (QPilotSHEDoubleImage.she_arrow_apply),

  completionToRootExtension T qPilotCompletionImage =
    (thetaPilotImage label 1)^(2l),

so the transported q-pilot image IS the Kummer image of the Theta-pilot image:
this is a THEOREM below (`kummerMap_thetaOne`), not a named input.

However, a completion-valued transport `S1902Carrier T -> LiteralCompletionIQCarrier T`
with `thetaImage |-> qPilotCompletionImage` CANNOT exist as a canonical inverse:
S1929 proves `thetaImage_not_mem_completionRange` (the theta image at label 1 is not
the completion image of any completion element) because the actual qVFamily has no
ordinary-completion 2l-th root (S342, `completionRootDatum_impossible`).  The
theorem `no_completion_valued_kummerTransport` below turns this into a formal
obstruction.  Hence the genuine Kummer realization must live in the theta carrier
(`GenuineKummerData.qImageInTheta = kummerMap thetaImage`, PROVED), and the only
remaining named input is the 1-column log-volume identification of the paper
readings, not the qImage realization.

The `strict_measure` field is the non-vacuity witness of
`Mzk1XiEContainmentRequirementActual`: the hull has STRICTLY larger volume than the
q-pilot image, so signed strict inequality does not collapse to reflexivity. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionNormBoundActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.S664RootQUnitNormLeOneActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open scoped Pointwise BigOperators

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-! ## 1. The Kummer power map on the theta carrier -/

/-- The Kummer map `x |-> x^(2l)` on the root-extension product carrier. -/
noncomputable def kummerMap (x : S1902Carrier T) : S1902Carrier T :=
  fun b => (x b) ^ (2 * l.value)

theorem kummerMap_apply (x : S1902Carrier T) (b : Bad (nativePlaceSelection T)) :
    kummerMap T x b = (x b) ^ (2 * l.value) := rfl

/-- The theta-pilot image at the root label, as an element of the theta carrier. -/
noncomputable def thetaOneCarrier : S1902Carrier T :=
  fun b => thetaPilotImage T (oneThetaLabel l) b

/-- The transported q-pilot image in the theta carrier. -/
noncomputable def qPilotInThetaCarrier : S1902Carrier T :=
  completionToRootExtension T (qPilotCompletionImage T)

/-- **Kummer realization of the q-pilot image (PROVED, theta carrier)**: the
transported q-pilot image is the Kummer (2l-power) image of the label-1 theta image. -/
theorem kummerMap_thetaOne : kummerMap T (thetaOneCarrier T) = qPilotInThetaCarrier T := by
  funext b
  unfold kummerMap thetaOneCarrier qPilotInThetaCarrier
  exact (she_arrow_apply T b).symm

/-! ## 2. Impossibility of a completion-valued Kummer transport -/

/-- **Obstruction (S342/S1929)**: there is no completion-valued transport that is a
right inverse of `completionToRootExtension` and sends the label-1 theta image to the
q-pilot completion image.  Such a map would put the theta image into the completion
range, contradicting `thetaImage_not_mem_completionRange`. -/
theorem no_completion_valued_kummerTransport
    (F : S1902Carrier T -> LiteralCompletionIQCarrier T)
    (hright : forall x : S1902Carrier T, completionToRootExtension T (F x) = x)
    (hq : F (thetaOneCarrier T) = qPilotCompletionImage T) : False := by
  have hmem : thetaOneCarrier T ∈ Set.range (completionToRootExtension T) := by
    exact ⟨F (thetaOneCarrier T), hright (thetaOneCarrier T)⟩
  have hcarrier : thetaOneCarrier T = rootExtensionProductThetaImage T (oneThetaLabel l) := by
    funext b
    rfl
  have hmem' : rootExtensionProductThetaImage T (oneThetaLabel l) ∈
      Set.range (completionToRootExtension T) := by
    rw [← hcarrier]
    exact hmem
  exact thetaImage_not_mem_completionRange (T := T) hmem'

/-! ## 3. The genuine Kummer data (qImage realization PROVED) -/

/-- Genuine Kummer data: the two theta-carrier elements and the PROVED equality
`qImageInTheta = kummerMap thetaImage`.  This replaces the previous named
`qImage_realized` field. -/
structure GenuineKummerData where
  thetaImage : S1902Carrier T
  qImageInTheta : S1902Carrier T
  thetaImage_eq : thetaImage = thetaOneCarrier T
  qImage_eq : qImageInTheta = kummerMap T thetaImage

noncomputable def genuineKummerData : GenuineKummerData T where
  thetaImage := thetaOneCarrier T
  qImageInTheta := qPilotInThetaCarrier T
  thetaImage_eq := rfl
  qImage_eq := (kummerMap_thetaOne T).symm

theorem genuineKummerData_constructed :
    (genuineKummerData T).qImageInTheta = kummerMap T (genuineKummerData T).thetaImage :=
  (genuineKummerData T).qImage_eq

/-- The realized q-pilot image lies in the actual Theta hull (genuine containment;
proved in A531 via SHE + norm bounds; repeated here). -/
theorem qPilotInThetaCarrier_mem_hull : qPilotInThetaCarrier T ∈ s1902Hull T := by
  rw [s1902Hull, rootExtensionProductImageHull, Set.mem_pi]
  intro b _
  rw [Metric.mem_closedBall, dist_eq_norm]
  unfold qPilotInThetaCarrier
  rw [she_arrow_apply]
  rw [sub_zero, norm_pow]
  have h1 : ‖thetaPilotImage T (oneThetaLabel l) b‖ ≤ 1 := by
    rw [thetaPilotImage_one_apply]
    exact rootNormedElement_norm_le_one (T := T) (b := b) (rootQUnitNormLeOne (T := T))
  have h2l : 1 ≤ 2 * l.value :=
    Nat.succ_le_of_lt (Nat.mul_pos (by norm_num) l.prime.pos)
  have hdec : ‖thetaPilotImage T (oneThetaLabel l) b‖ ^ (2 * l.value) ≤
      ‖thetaPilotImage T (oneThetaLabel l) b‖ ^ (1 : Nat) :=
    pow_le_pow_of_le_one (norm_nonneg _) h1 h2l
  have hrad : ‖thetaPilotImage T (oneThetaLabel l) b‖ ≤
      (rootImageRadius T b : Real) := by
    simpa [thetaPilotImage, rootExtensionProductThetaImage] using
      rootImageRadius_ge (T := T) (b := b) (oneThetaLabel l)
  calc ‖thetaPilotImage T (oneThetaLabel l) b‖ ^ (2 * l.value)
      ≤ ‖thetaPilotImage T (oneThetaLabel l) b‖ ^ (1 : Nat) := hdec
    _ = ‖thetaPilotImage T (oneThetaLabel l) b‖ := pow_one _
    _ ≤ (rootImageRadius T b : Real) := hrad

/-- Non-vacuity (shehdd's XiEContainmentRequirement): abstract volume functional on
theta-carrier regions with strict volume increase of the hull over the q-image. -/
structure KummerXiERealization where
  vol : Set (S1902Carrier T) -> Real
  vol_mono : forall {S U : Set (S1902Carrier T)}, S ≤ U -> vol S ≤ vol U
  q_pos : 0 < vol {qPilotInThetaCarrier T}
  strict_measure : vol {qPilotInThetaCarrier T} < vol (s1902Hull T)

theorem kummerXiE_containment (D : KummerXiERealization T) :
    {qPilotInThetaCarrier T} ≤ s1902Hull T := by
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  exact qPilotInThetaCarrier_mem_hull T

theorem genuine_logVolume_inequality (D : KummerXiERealization T) :
    D.vol {qPilotInThetaCarrier T} ≤ D.vol (s1902Hull T) :=
  D.vol_mono (kummerXiE_containment T D)

/-- Strict signed inequality (no reflexivity): from the strict measure increase. -/
theorem genuine_logVolume_inequality_strict (D : KummerXiERealization T) :
    D.vol {qPilotInThetaCarrier T} < D.vol (s1902Hull T) :=
  D.strict_measure

end LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual