/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealGeometryGapCards

/-!
# Mzk1QPilotSHEDoubleImageActual — q-pilot / Theta-pilot double image and the SHE arrow

A482 R4 (q-pilot / SHE side), on the LITERAL carriers only:

* q-pilot image: the actual q_V family of `S1929LiteralIQCarrierActual` /
  `QPilotZeroLocusDivisorActual.qVFamily` placed in the literal completion carrier
  `LiteralCompletionIQCarrier T = (b) -> K_b`; its log image is the actual local signed
  q-log `localSignedLog` of `ArithmeticQPilotLogVolume`;
* Theta-pilot image: the actual root-valued paper Theta image
  `rootExtensionProductThetaImage T` in the product root-extension carrier `S1902Carrier T`;
* the double image `QThetaDoubleImage` records both images and the root equation
  `thetaPilot ^ (2l) = completionToRootExtension qPilot` — the literal form of
  `q_v = (q[2u])^{2l}`;
* the SHE arrow (simultaneous holomorphic expressibility) is stated as the
  coordinatewise commuting-square equation between the two images and is PROVED;
* the same theta image is NOT in the completion subcarrier (S342 obstruction), so the
  SHE arrow is genuinely a simultaneous expression, not a completion identification.

No value-realization model is used. No sorry/axiom/placeholder. Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open scoped Pointwise

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The q-pilot image in the literal completion carrier: the actual q_V family at the
native bad places, placed in the corresponding local completion field. -/
noncomputable def qPilotCompletionImage : LiteralCompletionIQCarrier T :=
  fun b => ((qVFamily T b).q : rootBase T b)

/-- The literal q-pilot log image: the exact local signed q-log of the actual q_V family. -/
noncomputable def qPilotLogImage (b : Bad (nativePlaceSelection T)) : Real :=
  localSignedLog (qVFamily T b)

/-- The Theta-pilot image in the product root-extension carrier (literal paper values). -/
noncomputable def thetaPilotImage (j : ThetaLabel (l := l)) : S1902Carrier T :=
  rootExtensionProductThetaImage T j

/-- The exponential of the q-pilot log image is the actual completion norm of q_V. -/
theorem qPilotLogImage_exp (b : Bad (nativePlaceSelection T)) :
    Real.exp (qPilotLogImage T b) = ‖(qVFamily T b).q‖ := by
  rw [qPilotLogImage, localSignedLog_eq_neg_magnitude]
  exact exp_neg_localLogMagnitude (qVFamily T b)

/-- The Theta-pilot image at the label 1 is the actual root family. -/
theorem thetaPilotImage_one_apply (b : Bad (nativePlaceSelection T)) :
    thetaPilotImage T (oneThetaLabel l) b =
      (⟨rootNormedElement T b, rootNormedElement_mem T b⟩ : rootNormedExtension T b) := by
  have h := rootExtensionProductThetaImage_oneThetaLabel (T := T)
  exact congrFun h b

/-- The SHE arrow on the literal carriers: the completion q-pilot image is the
(2l)-th power of the Theta-pilot image at every bad place (simultaneous expression). -/
theorem she_arrow_apply (b : Bad (nativePlaceSelection T)) :
    completionToRootExtension T (qPilotCompletionImage T) b =
      (thetaPilotImage T (oneThetaLabel l) b) ^ (2 * l.value) := by
  rw [thetaPilotImage_one_apply, rootNormedElement_L_pow]
  rfl

/-- The SHE statement: coordinatewise simultaneity of the two literal images. -/
def SHEArrowStatement : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    completionToRootExtension T (qPilotCompletionImage T) b =
      (thetaPilotImage T (oneThetaLabel l) b) ^ (2 * l.value)

/-- PROVED SHE arrow on the literal carriers. -/
theorem sheArrowStatement_proved : SHEArrowStatement T := she_arrow_apply T

/-- The literal q-pilot / Theta-pilot double image with its root relation. -/
structure QThetaDoubleImage where
  qPilot : LiteralCompletionIQCarrier T
  thetaPilot : S1902Carrier T
  thetaPilot_is_label_one : thetaPilot = rootExtensionProductThetaImage T (oneThetaLabel l)
  root_relation : ∀ b : Bad (nativePlaceSelection T),
    completionToRootExtension T qPilot b = thetaPilot b ^ (2 * l.value)

/-- The actual double image built from the q_V family and the paper Theta image. -/
noncomputable def qThetaDoubleImage : QThetaDoubleImage T where
  qPilot := qPilotCompletionImage T
  thetaPilot := thetaPilotImage T (oneThetaLabel l)
  thetaPilot_is_label_one := rfl
  root_relation := she_arrow_apply T

/-- The Theta-pilot side of the double image is not in the completion subcarrier:
the SHE arrow is a genuine simultaneous expression, not a completion identification
(S342 obstruction; this is the literal-carrier no-go). -/
theorem thetaPilot_not_in_completionRange :
    rootExtensionProductThetaImage T (oneThetaLabel l) ∉
      Set.range (completionToRootExtension T) :=
  thetaImage_not_mem_completionRange (T := T)

/-- The q-pilot log image is a singleton (literal finite image); by the geometry gap
card its scaled unit-region realization is a compact bounded region. -/
theorem qPilotLogImage_bounded (b : Bad (nativePlaceSelection T)) :
    ∃ R : Real, 0 < R ∧
      ({qPilotLogImage T b} : Set Real) ⊆ R • Metric.closedBall (0 : Real) 1 :=
  isCompact_subset_smul_closedBall_unit isCompact_singleton

#check sheArrowStatement_proved
#check qThetaDoubleImage
#check thetaPilot_not_in_completionRange

end LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
end
