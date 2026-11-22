/- U-R C3 upper assembly (kurt): plug the actual lambda-weight packet values into the
accepted U-L hpaper assembly (Mzk1ULHpktActual).

Inputs (explicit, honest):
* hperB : per-b actual packet bound ksThetaHullLog b <= urPacketV_K b (delivered by
  Mzk1URPacketActualInstanceActual, currently in compile);
* hstepVIII : the Step(viii) intermediate weighted bound on Sum_b thetaLamWeight_b * urPacketV_K_b
  (david's Mzk1ULStepVIIIActual letters);
* hprime : l*_mod log(s<=) <= (4/3)*E_ar (paper prime-count bound);
then H_pkt <= kappa*(paperA - cL*Q) - M and theta_lambda <= that RHS.
Q = qPilotMagnitudePaper_v2 (v2, q scale), M = M_paper_v2.

Default heartbeats.
-/
import tmp.sheaf.xif.paper.Mzk1ULHpktActual
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import tmp.sheaf.xif.paper.Mzk1URThetaKHP5LamActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKC3UpperActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKHP5LamActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual
open MeasureTheory

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)]

/-- C3 upper: weighted actual packet values below the route RHS. -/
theorem C3_upper_route
    (S_ar E_ar Q M d_mod lstar_logs : ℝ) (hl : 0 < l.value) --
    (hE : 0 ≤ E_ar)
    (hprime : lstar_logs ≤ (4 / 3) * E_ar)
    (hconst : 2 * Real.log (l.value : ℝ) + 56 ≤ (4 / 9) * E_ar)
    (hstepVIII :
      (∑ b : Bad (nativePlaceSelection T),
          thetaLamWeight T b * urPacketV_K (l := l) T b) ≤
        kappa (l.value : ℝ) *
          ((1 + 12 * d_mod / (l.value : ℝ)) * S_ar +
            2 * Real.log (l.value : ℝ) + 56 -
            cL (l.value : ℝ) * Q +
            (20 / 3) * lstar_logs) - M) :
    ucWeightedHpkt (thetaLamWeight T) (fun b => urPacketV_K (l := l) T b) ≤
      kappa (l.value : ℝ) *
        (paperA d_mod (l.value : ℝ) S_ar E_ar - cL (l.value : ℝ) * Q) - M :=
  ul_hpaper_assembled
    (fun b : Bad (nativePlaceSelection T) => thetaLamWeight T b)
    (fun b => urPacketV_K (l := l) T b)
    (fun b => urPacketV_K (l := l) T b)
    (fun b => thetaLamWeight_nonneg T b) (fun b => le_rfl)
    (l.value : ℝ) S_ar E_ar Q M d_mod lstar_logs
    hl hE hprime hconst hstepVIII

/-- theta_lambda below the actual weighted packet value (C2 upper, from per-b inputs). -/
theorem theta_lam_le_Hpkt_of_hperB
    (hperB : ∀ b : Bad (nativePlaceSelection T),
      ksThetaHullLog (l := l) T b ≤ urPacketV_K (l := l) T b) :
    ksThetaHullLogRoot_lam (l := l) T ≤
      ucWeightedHpkt (thetaLamWeight T) (fun b => urPacketV_K (l := l) T b) :=
  ksThetaHullLogRoot_lam_le_ucWeightedHpkt_lam (l := l) T
    (fun b => urPacketV_K (l := l) T b) hperB

/-- End-to-end: theta_lambda <= kappa*(paperA - cL*Q) - M. -/
theorem theta_lam_le_paperRHS
    (hperB : ∀ b : Bad (nativePlaceSelection T),
      ksThetaHullLog (l := l) T b ≤ urPacketV_K (l := l) T b)
    (S_ar E_ar Q M d_mod lstar_logs : ℝ) (hl : 0 < l.value)
    (hE : 0 ≤ E_ar) (hprime : lstar_logs ≤ (4 / 3) * E_ar)
    (hconst : 2 * Real.log (l.value : ℝ) + 56 ≤ (4 / 9) * E_ar)
    (hstepVIII :
      (∑ b : Bad (nativePlaceSelection T),
          thetaLamWeight T b * urPacketV_K (l := l) T b) ≤
        kappa (l.value : ℝ) *
          ((1 + 12 * d_mod / (l.value : ℝ)) * S_ar +
            2 * Real.log (l.value : ℝ) + 56 -
            cL (l.value : ℝ) * Q + (20 / 3) * lstar_logs) - M) :
    ksThetaHullLogRoot_lam (l := l) T ≤
      kappa (l.value : ℝ) *
        (paperA d_mod (l.value : ℝ) S_ar E_ar - cL (l.value : ℝ) * Q) - M :=
  (theta_lam_le_Hpkt_of_hperB (l := l) T hperB).trans
    (C3_upper_route (l := l) T S_ar E_ar Q M d_mod lstar_logs hl hE hprime hconst hstepVIII)

#print axioms C3_upper_route
#print axioms theta_lam_le_Hpkt_of_hperB
#print axioms theta_lam_le_paperRHS


open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual in
/-- C3-upper last interface: hM from a per-b Q decomposition.

IMPORTANT caliber note (david audit, see C2-CALIBER-AUDIT section 4):
* The StepVIII Q : Bad -> R is the per-b LOCAL q quantity (c_norm_b * log p_b), and hM binds
  M = (Sum_b nativeBadLocalWeight_b * Q_b)/(2l). With Q_b := c_norm_b*log p_b this yields
  the LEGACY actualQ/(2l), NOT M_paper_v2 (the f_P/[F:Q] fibre weights differ).
* Therefore this lemma deliberately takes the decomposition hQ as an EXPLICIT hypothesis and
  does not assert "v2 = Sum nativeBadLocalWeight * Q". Under Lead ruling (A) (C3 uses the legacy
  caliber, docstring marked LEGACY) hQ instantiates with Q_b := c_norm_b*log p_b by the definition
  of actualQPilotMagnitudeClassical. Under ruling (B) the outer weight must be rebuilt at
  lambda/d_mod and a new per-b q quantity defined; that is a separate paper-faithful upgrade. -/
theorem C3_QM_alignment
    (Qb : Bad (nativePlaceSelection T) → ℝ)
    (hQ : qPilotMagnitudePaper_v2 (l := l) T =
      ∑ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b * Qb b) :
    M_paper_v2 (l := l) T =
      (∑ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b * Qb b) /
        (2 * (l.value : ℝ)) := by
  unfold M_paper_v2
  rw [hQ]

#print axioms C3_QM_alignment


open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual in
/-- INTERIM/LEGACY: the legacy Q/M caliber of C3-upper.

Q := actualQPilotMagnitudeClassical (sum_b nativeBadLocalWeight_b * c_norm_b * log p_b),
M := actualQPilotMagnitudeClassical/(2l). Under this caliber the StepVIII hM closes by rfl
(legacy_hM below), so the C3-upper assembly is immediate. This is INTERIM/LEGACY only: the
route-faithful Q is v2 = qPilotMagnitudePaper_v2 (paper Q_all, 1/[F:Q] fibre weights), and the
C2/C3 caliber unification is a separate unproven interface (see coord/Q-NORMALIZATION-AUDIT.md
and coord/C2-CALIBER-AUDIT.md sections 4, 9b). Not the final C3. -/
theorem C3_upper_route_legacy
    (S_ar E_ar d_mod lstar_logs : ℝ) (hl : 0 < l.value) (hE : 0 ≤ E_ar)
    (hprime : lstar_logs ≤ (4 / 3) * E_ar)
    (hconst : 2 * Real.log (l.value : ℝ) + 56 ≤ (4 / 9) * E_ar)
    (hstepVIII :
      (∑ b : Bad (nativePlaceSelection T),
          thetaLamWeight T b * urPacketV_K (l := l) T b) ≤
        kappa (l.value : ℝ) *
          ((1 + 12 * d_mod / (l.value : ℝ)) * S_ar +
            2 * Real.log (l.value : ℝ) + 56 -
            cL (l.value : ℝ) * actualQPilotMagnitudeClassical (l := l) T +
            (20 / 3) * lstar_logs) -
          actualQPilotMagnitudeClassical (l := l) T / (2 * (l.value : ℝ))) :
    ucWeightedHpkt (thetaLamWeight T) (fun b => urPacketV_K (l := l) T b) ≤
      kappa (l.value : ℝ) *
        (paperA d_mod (l.value : ℝ) S_ar E_ar -
          cL (l.value : ℝ) * actualQPilotMagnitudeClassical (l := l) T) -
        actualQPilotMagnitudeClassical (l := l) T / (2 * (l.value : ℝ)) :=
  C3_upper_route (l := l) T S_ar E_ar
    (actualQPilotMagnitudeClassical (l := l) T)
    (actualQPilotMagnitudeClassical (l := l) T / (2 * (l.value : ℝ)))
    d_mod lstar_logs hl hE hprime hconst hstepVIII

/-- INTERIM/LEGACY: StepVIII's hM closes by rfl in the legacy caliber. -/
theorem legacy_hM :
    (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          (QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b *
            Real.log (qVFamTensorP T b : ℝ))) =
      actualQPilotMagnitudeClassical (l := l) T := rfl

#print axioms C3_upper_route_legacy
#print axioms legacy_hM

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKC3UpperActual
end