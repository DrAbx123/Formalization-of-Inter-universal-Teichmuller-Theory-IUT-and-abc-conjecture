/- C3-upper lambda-weighted StepVIII (kurt): instantiate hstepVIII_of_collectionLayer_gen with
w := thetaLamWeight, Q := Qloc, M := M_paper_v2, hM := hM_lambda.

Reuse (DONE):
* Mzk1ULStepVIIILambdaActual.hstepVIII_of_collectionLayer_gen (DONE 12:48:49);
* Mzk1URThetaKHMLambdaActual.hM_lambda (DONE 13:11:48);
* Mzk1ULHlogKHSULambdaStatementsActual.HlogKLambdaData / HsQrawLambdaData (DONE 10:03:26).

Explicit OBLIGATIONS kept visible (not proved here, listed in coord/KURT-H-PARAM-AUDIT.md):
  hQ0 : forall b, 0 <= Qloc b  (positivity of the per-b local q quantity),
  hlog_half : Real.log l <= l/2 (arithmetic side condition for the letter conversions; true for
              l >= 5, easy to prove, kept explicit here).

Default heartbeats.
-/
import tmp.sheaf.xif.paper.Mzk1ULStepVIIILambdaActual
import tmp.sheaf.xif.paper.Mzk1URThetaKHMLambdaActual
import tmp.sheaf.xif.paper.Mzk1ULHlogKHSULambdaStatementsActual
import tmp.sheaf.xif.paper.Mzk1ULQbNonnegActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKStepVIIILambdaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQbVecActual
open LeanFormal.IUT.XiFPaper.Mzk1ULThetaLamWeightPosActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKHMLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1ULStepVIIILambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHlogKHSULambdaStatementsActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQbNonnegActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable [DecidableEq qVFamTensorV]

open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual in
/-- Lambda-weighted StepVIII intermediate bound, with the paper H_pkt weights. -/
theorem hstepVIII_lambdaWeights
    (X : ℕ) (hX : ∀ b : Bad (nativePlaceSelection T), qVFamTensorP T b ≤ X)
    (n : ℕ) (hn : 2 ≤ n) (hl_eq : (l.value : ℝ) = 2 * (n : ℝ) + 1)
    (S_ar d_mod : ℝ) (hl : 5 ≤ (l.value : ℝ))
    (D T' logP : Bad (nativePlaceSelection T) → ℝ)
    (Vh : Bad (nativePlaceSelection T) → ℕ → ℝ)
    (hlogP : ∀ b, logP b = Real.log (qVFamTensorP T b : ℝ))
    (hVh : ∀ i, ∀ label ∈ Finset.Icc 1 n,
      Vh i label ≤ LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
        (2 * (n : ℝ) + 1) (D i) (Qloc (T := T) i) (logP i) (T' i) label)
    (hQ0 : ∀ i, 0 ≤ Qloc (T := T) i)
    (hD0 : ∀ i, 0 ≤ D i) (hT0 : ∀ i, 0 ≤ T' i)
    (hii : (1 + 4 / (l.value : ℝ)) *
          (∑ i : Bad (nativePlaceSelection T), thetaLamWeight (l := l) T i * D i)
        ≤ (1 + 4 / (l.value : ℝ)) * S_ar + 2 * Real.log (l.value : ℝ) + 46)
    (hsQ : (4 / (l.value : ℝ)) *
          ((∑ i : Bad (nativePlaceSelection T), thetaLamWeight (l := l) T i) *
            Real.log (LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual.urSQ X : ℝ))
        ≤ (8 * d_mod / (l.value : ℝ)) * S_ar + 6)
    (hS_ar : 0 ≤ S_ar) (hd_mod : 1 ≤ d_mod) :
    (∑ i : Bad (nativePlaceSelection T),
        thetaLamWeight (l := l) T i * ((1 / (n : ℝ)) *
          (∑ label ∈ Finset.Icc 1 n, Vh i label)))
      ≤ LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual.kappa (l.value : ℝ) *
          ((1 + 12 * d_mod / (l.value : ℝ)) * S_ar
            + 2 * Real.log (l.value : ℝ) + 56
            - LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual.cL (l.value : ℝ) *
              (∑ i : Bad (nativePlaceSelection T),
                thetaLamWeight (l := l) T i * Qloc (T := T) i)
            + (20 / 3) * (∑ i : Bad (nativePlaceSelection T),
                thetaLamWeight (l := l) T i * T' i))
        - M_paper_v2 (T := T) := by
  have hper := hM_lambda (l := l) T
  have hconv : (∑ i : Bad (nativePlaceSelection T),
        thetaLamWeight (l := l) T i * Qloc (T := T) i) / (2 * (l.value : ℝ))
      = (∑ i : Bad (nativePlaceSelection T), Qb (T := T) i) / (2 * (l.value : ℝ)) := by
    rw [Finset.sum_congr rfl (fun b _ => thetaLamWeight_mul_Qloc (T := T) b)]
  exact hstepVIII_of_collectionLayer_gen (l := l) T
    (fun b => thetaLamWeight (l := l) T b) (fun b => thetaLamWeight_nonneg T b)
    X hX n hn hl_eq S_ar (M_paper_v2 (T := T)) d_mod hl D (Qloc (T := T)) T' logP Vh
    hlogP hVh hper hD0 hQ0 hT0 hii hsQ hS_ar hd_mod

#print axioms hstepVIII_lambdaWeights


/-- Auxiliary log bound: for x >= 5, log x <= x/2. -/
theorem log_half_of_five (x : ℝ) (hx : 5 ≤ x) : Real.log x ≤ x / 2 := by
  have hxpos : 0 < x := by linarith
  have hhalf : 0 < x / 2 := by linarith
  have hmul : x = 2 * (x / 2) := by ring
  rw [hmul, Real.log_mul (by norm_num) (ne_of_gt hhalf)]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogh : Real.log (x / 2) ≤ x / 2 - 1 := Real.log_le_sub_one_of_pos hhalf
  linarith

/-- Arithmetic conversion: HlogKLambdaData shape -> hstepVIII_of_collectionLayer_gen's hii. -/
theorem hii_convert {ll S X : ℝ} (hl : 5 ≤ ll)
    (hX : X ≤ S + 2 * Real.log ll + 21) :
    (1 + 4 / ll) * X ≤ (1 + 4 / ll) * S + 2 * Real.log ll + 46 := by
  have hlpos : 0 < ll := by linarith
  have hlog := log_half_of_five ll hl
  have hcoef : 0 ≤ 1 + 4 / ll := by positivity
  have hmul := mul_le_mul_of_nonneg_left hX hcoef
  have hkey : (1 + 4 / ll) * (2 * Real.log ll + 21) ≤ 2 * Real.log ll + 46 := by
    have hb : (4 / ll) * (2 * Real.log ll + 21) ≤ (4 / ll) * (ll + 21) := by
      gcongr
      linarith
    have hc : (4 / ll) * (ll + 21) = 4 + 84 / ll := by
      field_simp
      ring
    have h84 : 84 / ll ≤ 84 / 5 :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) hl
    nlinarith
  have hmul' : (1 + 4 / ll) * X ≤ (1 + 4 / ll) * S + (2 * Real.log ll + 21) + (4 / ll) * (2 * Real.log ll + 21) := by
    calc (1 + 4 / ll) * X ≤ (1 + 4 / ll) * (S + 2 * Real.log ll + 21) := hmul
      _ = (1 + 4 / ll) * S + (2 * Real.log ll + 21) + (4 / ll) * (2 * Real.log ll + 21) := by ring
  nlinarith

/-- Arithmetic conversion: HsQrawLambdaData shape -> hstepVIII_of_collectionLayer_gen's hsQ. -/
theorem hsQ_convert {ll d S Y : ℝ} (hl : 5 ≤ ll)
    (hY : Y ≤ 2 * d * S + 5 + Real.log ll) :
    (4 / ll) * Y ≤ (8 * d / ll) * S + 6 := by
  have hlpos : 0 < ll := by linarith
  have hlog := log_half_of_five ll hl
  have hcoef : 0 ≤ 4 / ll := by positivity
  have hmul := mul_le_mul_of_nonneg_left hY hcoef
  have hkey : (4 / ll) * (5 + Real.log ll) ≤ 6 := by
    have hb : (4 / ll) * (5 + Real.log ll) ≤ (4 / ll) * (5 + ll / 2) := by
      gcongr
    have hc : (4 / ll) * (5 + ll / 2) = 20 / ll + 2 := by
      field_simp
      ring
    have h20 : 20 / ll ≤ 20 / 5 :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) hl
    nlinarith
  have hmul' : (4 / ll) * Y ≤ (8 * d / ll) * S + (4 / ll) * (5 + Real.log ll) := by
    calc (4 / ll) * Y ≤ (4 / ll) * (2 * d * S + 5 + Real.log ll) := hmul
      _ = (8 * d / ll) * S + (4 / ll) * (5 + Real.log ll) := by ring
  nlinarith

#print axioms log_half_of_five
#print axioms hii_convert
#print axioms hsQ_convert


/-- Positivity of Qloc, from david's Qb_nonneg and thetaLamWeight_pos. -/
theorem hQ0_lambda (b : Bad (nativePlaceSelection T)) : 0 ≤ Qloc (T := T) b := by
  unfold Qloc
  exact div_nonneg (Qb_nonneg (T := T) b) (thetaLamWeight_pos (l := l) T b).le

#print axioms hQ0_lambda

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKStepVIIILambdaActual
end