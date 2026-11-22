import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual
import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import tmp.sheaf.xif.paper.Mzk1KummerRealizationActual
import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# A537 final Cor 3.12 checks: Kummer projection vs genuine xi-e content

Audit of `Mzk1Cor312FinalAssemblyActual`:
* `requirementOfReading` sets `thetaPossibleImages := {qPilotInThetaCarrier}`
  and `qRegion := {qPilotInThetaCarrier}`; hence `q_in_possible` is the
  **definitional projection of the Kummer realization** (kummerMap_thetaOne: theta_1 -> q),
  NOT the xi-e content.  The real xi-e content is `possible_in_hull :=
  kummerXiE_containment` (proved from the norm bound, not rfl), and the non-vacuity
  content is carried by `strict_measure : vol qRegion < vol hullRegion`, not by the
  subset field.
* `no_defeq_vacuity` (strict signed inequality) is proved from the strict measure,
  not from definitional containment.
* `target_matches_paper` records the exact IUT III 10324-10353 shape
  `-|log q| <= -|log Theta|`; both readings are linked to the realized log-volumes
  by the explicit `PaperKummerReading` fields.

Assumption table of the final chain:
PROVED: SHE root relation / qImage realization (KummerTransport/KummerRealization);
        qPilotInThetaCarrier_mem_hull; s1902Hull compact/finite;
        log-volume monotonicity; strict_measure signed strict inequality.
NAMED: PaperKummerReading.qReading_log/thetaReading_log (1-column readout);
       KummerXiERealization.vol/q_pos/strict_measure; q_negative on the signed q value.
NOT USED: definitional MRRep.reg containment, True fields, constant region as evidence.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalChecksV3Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- FLAG (A537): the final requirement's `q_in_possible` is the
**definitional projection of the Kummer realization** (q = kummerMap theta_1), not the
xi-e content.  The xi-e content is `possible_in_hull` (= `kummerXiE_containment`,
a theorem) and `strict_measure` (named). -/
theorem final_requirement_definitional_containment (R : PaperKummerReading T) :
    (requirementOfReading T R).qRegion =
      (requirementOfReading T R).thetaPossibleImages := rfl

/-- The REAL xi-e content of the final requirement: the realized q-pilot image lies in
the actual Theta hull (`kummerXiE_containment`, from the norm bound; not rfl). -/
theorem final_possible_in_hull (R : PaperKummerReading T) :
    ((requirementOfReading T R).qRegion : Set (S1902Carrier T)) ⊆
      (requirementOfReading T R).hullRegion :=
  LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual.kummerXiE_containment (T := T) R.D

/-- The unique named input of the final requirement: strict volume increase. -/
theorem final_strict_measure (R : PaperKummerReading T) :
    R.D.vol {qPilotInThetaCarrier T} < R.D.vol (s1902Hull T) :=
  R.D.strict_measure

/-- The non-vacuity is the strict measure/strict signed inequality. -/
theorem no_defeq_vacuity (R : PaperKummerReading T) :
    requirementSignedQ (requirementOfReading T R) <
      requirementSignedTheta (requirementOfReading T R) :=
  requirement_strict_signed (requirementOfReading T R)

theorem no_defeq_vacuity_ne (R : PaperKummerReading T) :
    requirementSignedQ (requirementOfReading T R) ≠
      requirementSignedTheta (requirementOfReading T R) :=
  ne_of_lt (no_defeq_vacuity T R)

/-- The assembled q/Theta slots are exactly the paper readings. -/
theorem final_contract_readings (R : PaperKummerReading T)
    (hqneg : requirementSignedQ (requirementOfReading T R) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    (cor312Contract_final T R hqneg ipl hipl she hshe apt hapt).qSigned = R.qReading ∧
      (cor312Contract_final T R hqneg ipl hipl she hshe apt hapt).thetaSigned =
        R.thetaReading := by
  constructor
  · simpa [cor312Contract_final, requirementContract, signedCor312Contract] using
      LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual.no_defeq_vacuity T R
  · simpa [cor312Contract_final, requirementContract, signedCor312Contract] using
      LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual.target_matches_paper T R


/-! ## A537 distinction summary and paper statement -/

/-- **The three parts kept distinct**: (1) the possible-image set is definitionally the
  q-region (projection of the Kummer realization); (2) q lies in the actual hull by the
  PROVED `kummerXiE_containment`; (3) the strict volume increase is the named input. -/
theorem distinction_summary (R : PaperKummerReading T) :
    (requirementOfReading T R).qRegion = (requirementOfReading T R).thetaPossibleImages ∧
      ({qPilotInThetaCarrier T} : Set (S1902Carrier T)) ⊆ s1902Hull T ∧
      R.D.vol {qPilotInThetaCarrier T} < R.D.vol (s1902Hull T) :=
  ⟨rfl,
   LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual.kummerXiE_containment (T := T) R.D,
   R.D.strict_measure⟩

/-- **The paper statement** (IUT III Cor 3.12, lines 10324-10353): there are real
  `qLog`, `thetaLog` with `qLog` the realized q-pilot log-volume, `thetaLog` the
  realized Theta-hull log-volume, `qLog <= thetaLog`, and `C >= -1` for every `C` with
  `thetaLog <= C * (-qLog)`; the strict reading gives `qLog < thetaLog`. -/
theorem paper_statement (R : PaperKummerReading T)
    (hqneg : requirementSignedQ (requirementOfReading T R) < 0) :
    ∃ qLog thetaLog : ℝ,
      qLog = Real.log (R.D.vol {qPilotInThetaCarrier T}) ∧
      thetaLog = Real.log (R.D.vol (s1902Hull T)) ∧
      qLog < thetaLog ∧
      (∀ C : ℝ, thetaLog ≤ C * (-qLog) → -1 ≤ C) := by
  have hqeq : R.qReading = requirementSignedQ (requirementOfReading T R) :=
    (LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual.no_defeq_vacuity T R).symm
  have hqneg' : R.qReading < 0 := by rw [hqeq]; exact hqneg
  refine ⟨R.qReading, R.thetaReading, R.qReading_log, R.thetaReading_log, ?_, ?_⟩
  · exact paperKummerReading_strict T R
  · intro C hC
    have hqpos : 0 < -R.qReading := neg_pos.mpr hqneg'
    have h1 : R.qReading < C * (-R.qReading) :=
      lt_of_lt_of_le (paperKummerReading_strict T R) hC
    have h2 : R.qReading / (-R.qReading) < C := (div_lt_iff₀ hqpos).mpr h1
    have h3 : R.qReading / (-R.qReading) = -1 := by
      have hqne : R.qReading ≠ 0 := ne_of_lt hqneg'
      field_simp
      ring
    rw [h3] at h2
    linarith
end LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalChecksV3Actual

end
