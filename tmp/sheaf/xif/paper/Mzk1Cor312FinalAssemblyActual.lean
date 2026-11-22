import tmp.sheaf.xif.paper.Mzk1KummerRealizationActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import tmp.sheaf.xif.paper.Mzk1SignedLogVolumeCor312Actual
import tmp.sheaf.xif.paper.Mzk1SignedCor312ContractActual

/-! # Cor 3.12 final assembly: genuine Kummer xi-e realization to Cor312Conclusion

Paper shape (IUT III:10324-10353): qSigned = -|log q|, thetaSigned = -|log Theta|,
the genuine containment gives qSigned ≤ thetaSigned. Only named input: the paper
1-column reading identification `PaperKummerReading.qReading_log/thetaReading_log`.

Three distinct ingredients (A537):
1. `q_in_possible := fun _ hx => hx` is a **definitional projection of the Kummer
   realization** (`kummerMap_thetaOne`: theta_1 maps to q, so q lies in the theta-side
   possible images by construction) — acceptable as `rfl`, it is NOT the xi-e content.
2. `possible_in_hull := kummerXiE_containment ...` is the **real xi-e content**
   (q in `s1902Hull`, proved from the norm bound, not `rfl`).
3. `strict_measure` (strict Haar volume increase of the hull) is the **only named
   input** of the requirement; it is not derivable from definitions. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedLogVolumeCor312Actual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The genuine xi-e requirement built from the realized q-pilot image and the
actual Theta hull; containment is the proved `kummerXiE_containment`. -/
noncomputable def requirementOfReading (R : PaperKummerReading T) :
    XiEContainmentRequirement (S1902Carrier T) R.D.vol where
  qRegion := {qPilotInThetaCarrier T}
  thetaPossibleImages := {qPilotInThetaCarrier T}
  hullRegion := s1902Hull T
  q_in_possible := fun _ hx => hx
  possible_in_hull := kummerXiE_containment (T := T) R.D
  q_pos := R.D.q_pos
  strict_measure := R.D.strict_measure

/-- `q_in_possible` is the definitional/reflexive component of the requirement
  (qRegion = thetaPossibleImages = {qPilot}); it is NOT the xi-e content. -/
theorem q_in_possible_is_reflexive (R : PaperKummerReading T) :
    (requirementOfReading T R).qRegion =
      (requirementOfReading T R).thetaPossibleImages := rfl

/-- `possible_in_hull` is the genuine xi-e content: the actual q-pilot image lies
  in the Theta hull (`kummerXiE_containment`, proved from the norm bound). -/
theorem possible_in_hull_genuine (R : PaperKummerReading T) :
    (requirementOfReading T R).thetaPossibleImages ⊆
      (requirementOfReading T R).hullRegion :=
  kummerXiE_containment (T := T) R.D

/-- Self-check: the assembled q reading is the realized log-volume, not a
definitional union. -/
theorem no_defeq_vacuity (R : PaperKummerReading T) :
    requirementSignedQ (requirementOfReading T R) = R.qReading := by
  unfold requirementSignedQ signedLogVolume requirementOfReading
  exact (R.qReading_log).symm

/-- Self-check: the assembled Theta reading is the realized hull log-volume. -/
theorem target_matches_paper (R : PaperKummerReading T) :
    requirementSignedTheta (requirementOfReading T R) = R.thetaReading := by
  unfold requirementSignedTheta signedLogVolume requirementOfReading
  exact (R.thetaReading_log).symm

/-- The genuine log-volume inequality (xi-e) in sheet form: q signed ≤ Theta signed. -/
theorem genuine_logVolume_inequality_SHE (R : PaperKummerReading T) :
    requirementSignedQ (requirementOfReading T R) ≤
      requirementSignedTheta (requirementOfReading T R) :=
  requirement_signed_inequality (requirementOfReading T R)

/-- Final assembled StepXI contract: qSigned = realized q reading,
thetaSigned = realized Theta reading, target_le_theta by the genuine inequality. -/
noncomputable def cor312Contract_final (R : PaperKummerReading T)
    (hqneg : requirementSignedQ (requirementOfReading T R) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) : StepXIContract :=
  requirementContract (requirementOfReading T R) hqneg ipl hipl she hshe apt hapt

/-- The final Cor 3.12 conclusion. -/
theorem cor312Conclusion_final (R : PaperKummerReading T)
    (hqneg : requirementSignedQ (requirementOfReading T R) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (cor312Contract_final T R hqneg ipl hipl she hshe apt hapt) :=
  requirement_cor312 (requirementOfReading T R) hqneg ipl hipl she hshe apt hapt

end LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
