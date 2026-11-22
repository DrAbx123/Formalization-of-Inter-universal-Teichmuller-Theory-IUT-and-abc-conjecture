/- F-side C3/C4 terminal assembly (kurt), per Lead ruling switch to the F-side chain.

Route legality: all donors are DONE:
* Mzk1UCC4PaperActual.uc_c4_actual_paper_letters (DONE 2026-11-16 21:57:48): C4 from hP5/htheta/hstepVIII;
* Mzk1URThetaHullActual.ur_negM_le_Htheta (DONE 2026-11-16 13:02:55): -actualQPilotMagnitudeClassical <= actualThetaHullLogRoot;
* Mzk1P6P5ThetaHullControl2.thetaHullLog_le_ucHpkt (DONE 2026-11-16 15:05:51): per-b hull <= packetV implies
  actualThetaHullLogRoot <= ucWeightedHpkt w V with w := nativeBadLocalWeight;
* PaperLevelXiFTargetActual.actualTargetWeight_nonneg (:145).

LETTER MAPPING (F-side, route C3/C4):
  S_ar := SAr_tripodal T                (F-level, Lead final caliber)
  d_mod := dMod T, eMod := eMod T, eta_prm := etaPrm
  M := actualQPilotMagnitudeClassical T (classical Q-scale; hP5 uses this same M)
  Q := 2 * l * actualQPilotMagnitudeClassical T  (so that c_l Q = (l+1)/4 * 2l M = ... ; c_l*Q <= A is the C4 assertion)
  w := nativeBadLocalWeight T, V := packetV (per-b q-packet value), B with V <= B.
Residual inputs (not proved here, listed): F-side per-b hull <= packetV (hperB), and hstepVIII for the
weight family w := nativeBadLocalWeight with the paper constants above.

Default heartbeats.
-/
import tmp.sheaf.xif.paper.Mzk1UCC4PaperActual
import tmp.sheaf.xif.paper.Mzk1URThetaHullActual
import tmp.sheaf.xif.paper.Mzk1P6P5ThetaHullControl2
import tmp.sheaf.xif.paper.Mzk1ULHpktActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKC4FsideActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1P6P5ThetaHullControl2
open LeanFormal.IUT.XiFPaper.Mzk1UCC4PaperActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1ULEModActual
open LeanFormal.IUT.XiFPaper.Mzk1UCEtaPrmActual
open LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- F-side C4 with the paper letters fully instantiated and an explicit (Q,M) mapping. -/
theorem C4_fside_letters {ι : Type*} [Fintype ι] (w V B : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hVB : ∀ i, V i ≤ B i) (Q M : ℝ)
    (hl : 5 ≤ (l.value : ℝ))
    (hP5 : -M ≤ actualThetaHullLogRoot (l := l) T)
    (htheta : actualThetaHullLogRoot (l := l) T ≤
      LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual.ucWeightedHpkt w V)
    (hstepVIII :
      (∑ i : ι, w i * B i) ≤
        Mzk1P6C3C4Actual.kappa (l.value : ℝ) *
          ((1 + 12 * Mzk1ULPaperLettersActual.dMod T / (l.value : ℝ)) *
              Mzk1ULPaperLettersActual.SAr_tripodal T +
            2 * Real.log (l.value : ℝ) + 56 -
            Mzk1P6C3C4Actual.cL (l.value : ℝ) * Q +
            (20 / 3) * Mzk1ULHpktActual.paperLstarLogs (Mzk1ULEModActual.eMod T) (l.value : ℝ)) -
          M) :
    Mzk1P6C3C4Actual.cL (l.value : ℝ) * Q ≤
      Mzk1ULHpktActual.paperA (Mzk1ULPaperLettersActual.dMod T) (l.value : ℝ)
        (Mzk1ULPaperLettersActual.SAr_tripodal T)
        (Mzk1ULHpktActual.paperEar (Mzk1ULEModActual.eMod T) (l.value : ℝ)
          Mzk1UCEtaPrmActual.etaPrm) :=
  Mzk1UCC4PaperActual.uc_c4_actual_paper_letters (l := l) T w V B hw hVB Q M hl hP5 htheta hstepVIII

/-- Concrete F-side C4: w := nativeBadLocalWeight, M := actualQPilotMagnitudeClassical,
Q := 2*l*M. Residual explicit inputs: per-b F-side hull <= packetV (hperB) and hstepVIII. -/
theorem C4_fside_actual
    (packetV : Bad (nativePlaceSelection T) → ℝ)
    (hperB : ∀ b, actualLocalHullLog (l := l) T b ≤ packetV b)
    (hl : 5 ≤ (l.value : ℝ))
    (hstepVIII :
      (∑ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b * packetV b) ≤
        Mzk1P6C3C4Actual.kappa (l.value : ℝ) *
          ((1 + 12 * Mzk1ULPaperLettersActual.dMod T / (l.value : ℝ)) *
              Mzk1ULPaperLettersActual.SAr_tripodal T +
            2 * Real.log (l.value : ℝ) + 56 -
            Mzk1P6C3C4Actual.cL (l.value : ℝ) *
              (2 * (l.value : ℝ) * actualQPilotMagnitudeClassical (l := l) T) +
            (20 / 3) * Mzk1ULHpktActual.paperLstarLogs (Mzk1ULEModActual.eMod T) (l.value : ℝ)) -
          actualQPilotMagnitudeClassical (l := l) T) :
    Mzk1P6C3C4Actual.cL (l.value : ℝ) *
        (2 * (l.value : ℝ) * actualQPilotMagnitudeClassical (l := l) T) ≤
      Mzk1ULHpktActual.paperA (Mzk1ULPaperLettersActual.dMod T) (l.value : ℝ)
        (Mzk1ULPaperLettersActual.SAr_tripodal T)
        (Mzk1ULHpktActual.paperEar (Mzk1ULEModActual.eMod T) (l.value : ℝ)
          Mzk1UCEtaPrmActual.etaPrm) := by
  have hw : ∀ b : Bad (nativePlaceSelection T), 0 ≤ nativeBadLocalWeight T b :=
    fun b => actualTargetWeight_nonneg (l := l) T b
  have hVB : ∀ b, packetV b ≤ packetV b := fun b => le_rfl
  have htheta := thetaHullLog_le_ucHpkt (l := l) T packetV hperB
  have hP5 : -actualQPilotMagnitudeClassical (l := l) T ≤
      actualThetaHullLogRoot (l := l) T := ur_negM_le_Htheta (l := l) T
  exact C4_fside_letters (l := l) T _ packetV packetV hw hVB
    (2 * (l.value : ℝ) * actualQPilotMagnitudeClassical (l := l) T)
    (actualQPilotMagnitudeClassical (l := l) T) hl hP5 htheta hstepVIII

#print axioms C4_fside_letters
#print axioms C4_fside_actual

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKC4FsideActual
end