/- hstepVIII generalization (kurt): weight-generic StepVIII assembly.

Proof body is the collectionLayer proof with the outer weight parameterized to an arbitrary
nonnegative w (the pure-real StepVIII chain is linear in the weight). Instance w := thetaLamWeight
gives the paper-faithful C3 intermediate; w := nativeBadLocalWeight recovers the legacy version.

Default heartbeats.
-/
import tmp.sheaf.xif.paper.Mzk1ULStepVIIIActual
import tmp.sheaf.xif.paper.Mzk1P6C3C4Actual
import tmp.sheaf.xif.paper.Mzk1URSmallPrimeActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1ULStepVIIILambdaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1ULStepVIIIActual
open LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Weight-generic small-prime aggregation. -/
theorem weighted_logP_aggregate_le
    (w : Bad (nativePlaceSelection T) → ℝ) (hw : ∀ b, 0 ≤ w b)
    (X : ℕ) (hX : ∀ b : Bad (nativePlaceSelection T), qVFamTensorP T b ≤ X) :
    (∑ b : Bad (nativePlaceSelection T), w b * Real.log (qVFamTensorP T b : ℝ))
      ≤ (∑ b : Bad (nativePlaceSelection T), w b) * Real.log (urSQ X : ℝ) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum ?_
  intro b _
  have hlog : Real.log (qVFamTensorP T b : ℝ) ≤ Real.log (urSQ X : ℝ) :=
    ur_hlogp_le_logSQ T b X (hX b)
  exact mul_le_mul_of_nonneg_left hlog (hw b)

/-- Nonnegativity of a weighted aggregate. -/
theorem weighted_sum_nonneg (w A : Bad (nativePlaceSelection T) → ℝ)
    (hw : ∀ b, 0 ≤ w b) (hA : ∀ b, 0 ≤ A b) :
    0 ≤ ∑ b : Bad (nativePlaceSelection T), w b * A b :=
  Finset.sum_nonneg (fun b _ => mul_nonneg (hw b) (hA b))

/-- Weight-generic hstepVIII_of_collectionLayer (arbitrary nonnegative outer weight). -/
theorem hstepVIII_of_collectionLayer_gen
    (w : Bad (nativePlaceSelection T) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (X : ℕ) (hX : ∀ b : Bad (nativePlaceSelection T), qVFamTensorP T b ≤ X)
    (n : ℕ) (hn : 2 ≤ n) (hl_eq : (l.value : ℝ) = 2 * (n : ℝ) + 1)
    (S_ar M d_mod : ℝ) (hl : 5 ≤ (l.value : ℝ))
    (D Q T' logP : Bad (nativePlaceSelection T) → ℝ)
    (Vh : Bad (nativePlaceSelection T) → ℕ → ℝ)
    (hlogP : ∀ b, logP b = Real.log (qVFamTensorP T b : ℝ))
    (hVh : ∀ i, ∀ label ∈ Finset.Icc 1 n,
      Vh i label ≤ LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
        (2 * (n : ℝ) + 1) (D i) (Q i) (logP i) (T' i) label)
    (hM : M = (∑ i : Bad (nativePlaceSelection T), w i * Q i) / (2 * (l.value : ℝ)))
    (hD0 : ∀ i, 0 ≤ D i) (hQ0 : ∀ i, 0 ≤ Q i) (hT0 : ∀ i, 0 ≤ T' i)
    (hii : (1 + 4 / (l.value : ℝ)) *
          (∑ i : Bad (nativePlaceSelection T), w i * D i)
        ≤ (1 + 4 / (l.value : ℝ)) * S_ar + 2 * Real.log (l.value : ℝ) + 46)
    (hsQ : (4 / (l.value : ℝ)) *
          ((∑ i : Bad (nativePlaceSelection T), w i) * Real.log (urSQ X : ℝ))
        ≤ (8 * d_mod / (l.value : ℝ)) * S_ar + 6)
    (hS_ar : 0 ≤ S_ar) (hd_mod : 1 ≤ d_mod) :
    (∑ i : Bad (nativePlaceSelection T),
        w i * ((1 / (n : ℝ)) * (∑ label ∈ Finset.Icc 1 n, Vh i label)))
      ≤ LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual.kappa (l.value : ℝ) * ((1 + 12 * d_mod / (l.value : ℝ)) * S_ar
          + 2 * Real.log (l.value : ℝ) + 56
          - LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual.cL (l.value : ℝ) * (∑ i : Bad (nativePlaceSelection T), w i * Q i)
          + (20 / 3) * (∑ i : Bad (nativePlaceSelection T), w i * T' i))
        - M := by
  classical
  have hγ0 : ∀ i, 0 ≤ w i :=
    fun i => hw i
  have hQ : 0 ≤ ∑ i : Bad (nativePlaceSelection T),
      w i * Q i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hγ0 i) (hQ0 i))
  have hlogDK : 0 ≤ ∑ i : Bad (nativePlaceSelection T),
      w i * D i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hγ0 i) (hD0 i))
  have hlstar : 0 ≤ ∑ i : Bad (nativePlaceSelection T),
      w i * T' i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hγ0 i) (hT0 i))
  have hlogSQ : 0 ≤ (∑ i : Bad (nativePlaceSelection T),
        w i)
      * Real.log (LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual.urSQ X : ℝ) := by
    have hγsum : 0 ≤ ∑ i : Bad (nativePlaceSelection T),
        w i :=
      Finset.sum_nonneg (fun i _ => hγ0 i)
    have hX1 : (1 : ℝ) ≤ (LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual.urSQ X : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt
        (LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual.urSQ_pos X)
    exact mul_nonneg hγsum (Real.log_nonneg hX1)
  have hlogP_le : (∑ i : Bad (nativePlaceSelection T),
        w i * logP i)
      ≤ (∑ i : Bad (nativePlaceSelection T),
          w i)
        * Real.log
          (LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual.urSQ X : ℝ) := by
    have h := weighted_logP_aggregate_le (l := l) T w hw X hX
    calc (∑ i : Bad (nativePlaceSelection T),
          w i * logP i)
        = ∑ i : Bad (nativePlaceSelection T),
            w i
              * Real.log
                (LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual.qVFamTensorP T i : ℝ) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hlogP i]
      _ ≤ _ := h
  have hviT := LeanFormal.IUT.XiFPaper.Mzk1ULHviTableFinalActual.hviTable_final
    (b := Bad (nativePlaceSelection T))
    (fun i => w i)
    hγ0 n hn logP D Q T' Vh hVh
  refine hstepVIII_of_retained
    ({ l := (l.value : ℝ), S_ar := S_ar,
       Q := (∑ i : Bad (nativePlaceSelection T),
          w i * Q i),
       M := M, d_mod := d_mod,
       lstar := (∑ i : Bad (nativePlaceSelection T),
          w i * T' i),
       logDK := (∑ i : Bad (nativePlaceSelection T),
          w i * D i),
       logSQ := (∑ i : Bad (nativePlaceSelection T),
          w i)
          * Real.log (LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual.urSQ X : ℝ),
       logP := (∑ i : Bad (nativePlaceSelection T),
          w i * logP i),
       arch := 0,
       s3014 := (∑ i : Bad (nativePlaceSelection T),
          w i
            * ((1 / (n : ℝ)) * (∑ label ∈ Finset.Icc 1 n, Vh i label))),
       n := n, hl := hl, hn := hn, hl_eq := hl_eq, hQ := hQ, hM := hM,
       hlogDK := hlogDK, hlogSQ := hlogSQ, hlstar := hlstar,
       hii := hii, hsQ := hsQ, hS_ar := hS_ar, hd_mod := hd_mod,
       hvii := by
         have hpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
         have : (0 : ℝ) ≤ ((l.value : ℝ) + 5) / 4 := by positivity
         positivity } :
      PaperStepVIIIRetained (Bad (nativePlaceSelection T)))
    (fun i => w i)
    (fun i => (1 / (n : ℝ)) * (∑ label ∈ Finset.Icc 1 n, Vh i label))
    rfl hlogP_le (by simpa using hviT)
end LeanFormal.IUT.XiFPaper.Mzk1ULStepVIIILambdaActual
end