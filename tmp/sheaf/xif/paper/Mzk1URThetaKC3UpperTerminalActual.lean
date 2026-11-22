/- C3-upper terminal form (kurt): LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperA form from the lambda-weighted StepVIII bound.

Reuse (DONE):
* Mzk1ULStepVIIILambdaActual.hstepVIII_lambdaWeights (DONE 13:30:27): the lambda-weighted
  intermediate with Qloc, M_paper_v2;
* LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.ul_hpaper_of_stepVIII / LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperA / kappa / cL (accepted C3-upper assembly);
* Mzk1ULP6C3C4Actual.c3_to_c4 (C4 conclusion cL*Q <= A).

OBLIGATIONS kept explicit (per-lambda instantiation; listed in coord/KURT-H-PARAM-AUDIT.md):
  hHpkt : H_pkt <= (sum_b thetaLamWeight_b * ((1/n) sum_{label} Vh b label))   (StepV per-label
          decomposition, instantiated per lambda);
  hprime : lstar_logs <= (4/3) E_ar; hconst : 2 log l + 56 <= (4/9) E_ar  (paper constants);
  per lambda: Q_hpkt := sum_b thetaLamWeight_b * Qloc_b (= lambda-weighted Q),_S := discOver K +
          truncConductor lam, M := M_paper_v2, lstar_logs := sum_b thetaLamWeight_b * T'_b.

Default heartbeats.
-/
import tmp.sheaf.xif.paper.Mzk1URThetaKStepVIIILambdaActual
import tmp.sheaf.xif.paper.Mzk1ULHpktActual
import tmp.sheaf.xif.paper.Mzk1P6C3C4Actual
import tmp.sheaf.xif.paper.Mzk1UHprimeActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKC3UpperTerminalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual

variable {l : PrimeGeFive}

/-- C3 upper in LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperA form, from the lambda-weighted StepVIII intermediate. -/
theorem C3_upper_route_lambda
    (S_ar E_ar Q d_mod lstar_logs H : ℝ) (hl : 0 < l.value) (hE : 0 ≤ E_ar)
    (hprime : lstar_logs ≤ (4 / 3) * E_ar)
    (hconst : 2 * Real.log (l.value : ℝ) + 56 ≤ (4 / 9) * E_ar)
    (hstepVIII :
      H ≤ LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual.kappa (l.value : ℝ) *
        ((1 + 12 * d_mod / (l.value : ℝ)) * S_ar +
          2 * Real.log (l.value : ℝ) + 56 -
          LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual.cL (l.value : ℝ) * Q + (20 / 3) * lstar_logs) - M) :
    H ≤ LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual.kappa (l.value : ℝ) * (LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperA d_mod (l.value : ℝ) S_ar E_ar - LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual.cL (l.value : ℝ) * Q) - M :=
  ul_hpaper_of_stepVIII (l.value : ℝ) S_ar E_ar Q M d_mod lstar_logs H
    hl hE hprime hconst hstepVIII

open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual in
/-- C4 conclusion (c_l Q <= A) from the C2 lower, C2 upper and the C3-upper LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperA bound. -/
theorem C4_of_C2_C3
    (Q A M theta Hpkt : ℝ)
    (hkappa : 0 < LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual.kappa (l.value : ℝ))
    (hP5 : -M ≤ theta) (htheta : theta ≤ Hpkt)
    (hC3 : Hpkt ≤ LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual.kappa (l.value : ℝ) * (A - LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual.cL (l.value : ℝ) * Q) - M) :
    LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual.cL (l.value : ℝ) * Q ≤ A :=
  c3_to_c4 (l.value : ℝ) A Q M Hpkt theta hkappa hP5 htheta hC3

#print axioms C3_upper_route_lambda
#print axioms C4_of_C2_C3


/-- hprime with the paper constants, filled from andrew's DONE thin instance. -/
theorem hprime_paper (eMod : ℕ) (he : 1 ≤ eMod) (hl : 1 ≤ (l.value : ℝ)) :
    LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperLstarLogs eMod (l.value : ℝ) ≤
      (4 / 3) * LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperEar eMod (l.value : ℝ) LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.etaPrm :=
  Mzk1UHprimeActual.hprime_paperLstarLogs_le (eMod := eMod) he hl

/-- hconst with the paper constants, filled from the accepted C3 assembly. -/
theorem hconst_paper (eMod : ℕ) (he : 1 ≤ eMod) (hl : 5 ≤ (l.value : ℝ))
    (heta : 0 ≤ LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.etaPrm) :
    2 * Real.log (l.value : ℝ) + 56 ≤
      (4 / 9) * LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperEar eMod (l.value : ℝ) LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.etaPrm :=
  ul_hconst_of_paperConstants (eMod := eMod) he le_rfl hl heta

/-- C3 upper in LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperA form with the paper constants, from the lambda-weighted StepVIII input. -/
theorem C3_upper_route_paperConstants
    (eMod : ℕ) (he : 1 ≤ eMod) (hl5 : 5 ≤ (l.value : ℝ)) (heta : 0 ≤ LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.etaPrm)
    (S_ar Q H : ℝ)
    (hstepVIII :
      H ≤ LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual.kappa (l.value : ℝ) *
        ((1 + 12 * LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual.dMod T / (l.value : ℝ)) * S_ar +
          2 * Real.log (l.value : ℝ) + 56 -
          LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual.cL (l.value : ℝ) * Q +
          (20 / 3) * LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperLstarLogs eMod (l.value : ℝ)) -
        LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 (T := T)) :
    H ≤ LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual.kappa (l.value : ℝ) *
      (LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperA (LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual.dMod T) (l.value : ℝ) S_ar (LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperEar eMod (l.value : ℝ) LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.etaPrm) -
        LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual.cL (l.value : ℝ) * Q) - LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 (T := T) := by
  have hl1 : 1 ≤ (l.value : ℝ) := by linarith
  have hl0 : 0 < (l.value : ℝ) := by linarith
  have hE : 0 ≤ LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperEar eMod (l.value : ℝ) LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.etaPrm :=
    LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperEar_nonneg (by linarith) heta
  exact C3_upper_route_lambda (l := l) S_ar (LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperEar eMod (l.value : ℝ) LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.etaPrm) Q
    (LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual.dMod T) (LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperLstarLogs eMod (l.value : ℝ)) H hl0 hE
    (hprime_paper (l := l) eMod he hl1) (hconst_paper (l := l) eMod he hl5 heta) hstepVIII

#print axioms hprime_paper
#print axioms hconst_paper
#print axioms C3_upper_route_paperConstants


open LeanFormal.IUT.XiFPaper.Mzk1URThetaKStepVIIILambdaActual in
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual in
open LeanFormal.IUT.XiFPaper.Mzk1ULQbVecActual in
open LeanFormal.IUT.XiFPaper.Mzk1ULThetaLamWeightPosActual in
/-- C3 upper in LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperA form with the lambda-weighted StepVIII bound FILLED IN from the DONE
generator. The only remaining input is the per-label StepV decomposition hHpkt (packet side). -/
theorem C3_upper_route_lambdaWeights
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (eMod : ℕ) (he : 1 ≤ eMod) (hl5 : 5 ≤ (l.value : ℝ)) (heta : 0 ≤ LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.etaPrm)
    (X : ℕ) (hX : ∀ b : Bad (nativePlaceSelection T),
      LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual.qVFamTensorP T b ≤ X)
    (n : ℕ) (hn : 2 ≤ n) (hl_eq : (l.value : ℝ) = 2 * (n : ℝ) + 1)
    (S_ar d_mod : ℝ) (hS_ar : 0 ≤ S_ar) (hd_mod : 1 ≤ d_mod)
    (D T' logP : Bad (nativePlaceSelection T) → ℝ)
    (Vh : Bad (nativePlaceSelection T) → ℕ → ℝ)
    (hlogP : ∀ b, logP b = Real.log (LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual.qVFamTensorP T b : ℝ))
    (hVh : ∀ i, ∀ label ∈ Finset.Icc 1 n,
      Vh i label ≤ LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
        (2 * (n : ℝ) + 1) (D i) (Qloc (T := T) i) (logP i) (T' i) label)
    (hD0 : ∀ i, 0 ≤ D i) (hT0 : ∀ i, 0 ≤ T' i)
    (hlogdK : (∑ i : Bad (nativePlaceSelection T),
        LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual.thetaLamWeight T i * D i) ≤ S_ar + 2 * Real.log (l.value : ℝ) + 21)
    (hsQraw : (∑ i : Bad (nativePlaceSelection T), LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual.thetaLamWeight T i) *
        Real.log (LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual.urSQ X : ℝ) ≤
      2 * d_mod * S_ar + 5 + Real.log (l.value : ℝ))
    (hHpkt : LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual.ucWeightedHpkt (LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual.thetaLamWeight T)
        (fun b => (1 / (n : ℝ)) * (∑ label ∈ Finset.Icc 1 n, Vh b label)) ≤
      (∑ i : Bad (nativePlaceSelection T),
        LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual.thetaLamWeight T i * ((1 / (n : ℝ)) *
          (∑ label ∈ Finset.Icc 1 n, Vh i label)))) :
    LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual.ucWeightedHpkt (LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual.thetaLamWeight T)
        (fun b => (1 / (n : ℝ)) * (∑ label ∈ Finset.Icc 1 n, Vh b label)) ≤
      LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual.kappa (l.value : ℝ) *
        (LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperA (LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual.dMod T) (l.value : ℝ) S_ar
            (LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperEar eMod (l.value : ℝ) LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.etaPrm) -
          LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual.cL (l.value : ℝ) *
            (∑ i : Bad (nativePlaceSelection T),
              LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual.thetaLamWeight T i * Qloc (T := T) i)) -
        LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2 (T := T) := by
  have hl1 : 1 ≤ (l.value : ℝ) := by linarith
  have hii := hii_convert (ll := (l.value : ℝ)) hl5 hlogdK
  have hsQ := hsQ_convert (ll := (l.value : ℝ)) (d := d_mod) (S := S_ar) hl5 hsQraw
  have hstepVIII_inst := hstepVIII_lambdaWeights (l := l) T X hX n hn hl_eq S_ar d_mod hl5
    D T' logP Vh hlogP hVh (fun i => hQ0_lambda (l := l) T i) hD0 hT0 hii hsQ hS_ar hd_mod
  exact hHpkt.trans (C3_upper_route_paperConstants (l := l) T eMod he hl5 heta S_ar
    (∑ i : Bad (nativePlaceSelection T),
      LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual.thetaLamWeight T i * Qloc (T := T) i) _ hstepVIII_inst)

#print axioms C3_upper_route_lambdaWeights

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKC3UpperTerminalActual
end