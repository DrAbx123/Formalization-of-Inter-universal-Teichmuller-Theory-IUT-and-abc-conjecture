/-
# U-C: IUT IV Step (viii) retained intermediate and the hstepVIII assembly

Route §5.4.3 item 3 keeps the paper's Step (viii) intermediate inequality as the
retained input of the P6-pre upper bound.  This file gives:

* elementary paper estimates that are proved here:
  log_pi_le_two (IUT IV (E6) log(pi) <= 2) and its consequence
  arch_container_le (IUT IV Step (vii), lines 1856-1859:
  (l+5)/4 * log(pi) <= (l+1)/4 * 4 for l >= 5);
* the structure PaperStepVIIIRetained with exactly three retained paper
  intermediate fields hiii / hvi / hvii, each with its paper citation and its
  LHS/RHS written out in the notation of the U-C chain;
* hstepVIII_of_retained: PURE ALGEBRA from the three retained fields to the
  hstepVIII consumed by Mzk1UCHpktActual.uc_c3_paperConstants.

The three retained fields are labelled RETAINED PAPER INTERMEDIATE, NO INHABITANT:
they are hypotheses of the theorems below (not axioms, not sorry, not surrogates).
Their proofs are the paper's Steps (ii)-(vii); the next rounds narrow them one by
one (hvi first) as the corresponding U-L donors are wired in.
-/
import tmp.sheaf.xif.paper.Mzk1ULHpktActual
import tmp.sheaf.xif.paper.Mzk1UCHpktActual
import tmp.sheaf.xif.paper.Mzk1P6StepVAveragesActual
import tmp.sheaf.xif.paper.Mzk1URThetaHthetaActual
import tmp.sheaf.xif.paper.Mzk1URSmallPrimeActual
import tmp.sheaf.xif.paper.Mzk1ULStepHiiHsQActual
import tmp.sheaf.xif.paper.Mzk1ULPaperLettersActual
import tmp.sheaf.xif.paper.Mzk1URBadWeightSumActual
import tmp.sheaf.xif.paper.Mzk1ULHviTableFinalActual
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULStepVIIIActual

open LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual
open LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual
open LeanFormal.IUT.XiFPaper.Mzk1P6StepVAveragesActual

/-! ## Elementary paper estimates (proved) -/

/-- IUT IV (E6): log(pi) <= 2.  Proof: pi < 4 and log 4 = 2 log 2 < 2. -/
theorem log_pi_le_two : Real.log Real.pi ≤ 2 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have h4 : Real.log Real.pi ≤ Real.log 4 := Real.log_le_log hπ Real.pi_lt_four.le
  have hflog : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [hflog] at h4
  linarith

/-- IUT IV Step (vii) final display (lines 1856-1859): for l >= 5,
(l+5)/4 * log(pi) <= (l+1)/4 * 4. -/
theorem arch_container_le {l : ℝ} (hl : 5 ≤ l) :
    (l + 5) / 4 * Real.log Real.pi ≤ (l + 1) / 4 * 4 := by
  have hpi := log_pi_le_two
  have h2 : (l + 5) / 4 * Real.log Real.pi ≤ (l + 5) / 4 * 2 := by
    apply mul_le_mul_of_nonneg_left hpi
    linarith
  have h3 : (l + 5) / 4 * 2 ≤ (l + 1) / 4 * 4 := by linarith
  linarith

/-! ## The retained paper Step (viii) intermediate -/

/-- RETAINED PAPER INTERMEDIATE, NO INHABITANT (fields hiii, hviPacket, hvii;
hviProcession is proved separately below).

Paper citations and LHS/RHS:

* hiii — Step (iii) combined display, IUT IV lines 1553-1582:
  (1 + 4/l)*log(dK) + (4/l)*log(s^Q)
     <= (1 + 12*d_mod/l)*S_ar + 2*log(l) + 52,
  with S_ar = log(d_Ftpd) + log(f_Ftpd), logDK = log(dK), logSQ = log(s^Q);

* hviPacket — RETAINED three-level averaging identification, IUT IV L1701-1783:
  sum_a w_a * B_a
     <= (1/n) * sum_{j in 1..n} collectionBound (2n+1) logDK Q logSQ lstar j + arch,
  with l = 2n+1; this is the only un-mechanised part of the averaging
  (symmetrization over i-dagger, weighted average over places, procession
  average over j);

* hvii — Step (vii) archimedean container bound (lines 1819-1859):
  arch <= (l+5)/4 * log(pi).

The final -M term of the paper display is -Q/(2*l) (hM); the paper estimate
(l+1)/4*(1/6)*(12/l^2) >= 1/(2l) (lines 1879-1883) turns the raw -(1/6)*Q into
-c_l*Q - Q/(2l) in the assembly. -/
structure PaperStepVIIIRetained (ι : Type*) [Fintype ι] where
  l : ℝ
  S_ar : ℝ
  Q : ℝ
  M : ℝ
  d_mod : ℝ
  lstar : ℝ
  logDK : ℝ
  logSQ : ℝ
  /-- logP = the AGGREGATED donor collection S slot: sum_b gamma_b * log p_b with
  p_b := qVFamTensorP T b (the per-b prime).  It comes from collectionChoiceBound's
  +1*log p term.  When the bad moduli share one rational prime
  (NativeBadModuliFixedPrime) this collapses to logP = (sum_b gamma_b) * log p.
  This is an aggregated letter (Lead 2026-11-17 ruling: no sum_gamma = 1; the
  d_mod normalization stays in the display coefficients (1+12 d_mod/l) and hiii). -/
  logP : ℝ
  arch : ℝ
  /-- s3014 = the bad-place weighted aggregate of the per-b procession-normalized
  collection hull volumes: sum over b of nativeBadLocalWeight T b * ((1/n) *
  sum_j weighted-average-over-collection of the actual hull normalized log-volume).
  The bad-place index and weights are the same as in actualThetaHullLogRoot /
  htheta (NOT normalized: no sum_gamma = 1 requirement is imposed here).

  Collection layer (Lead/kurt 2026-11-16 design): the paper collection
  {v_i}_{i=1..j+1} runs over the label-dependent collection, while the OLD reading
  via S3014ProcessionAverageBound uses the FIXED tensor-factor index set (its
  different sum sum_i d_i does not scale with j+1).  The donor layer
  StepVProcessionAverage.collectionChoiceBound / collectionBound uses the correct
  collection form: E = qVFamTensorV factors, lam = 1, d e = localNormOrder of the
  different, oq e = qVFamNormalizedCoefficient, logp = log p_b, iotaL = paper iota
  times l*_mod.  This field therefore denotes the donor-layer aggregation, and
  hviTable below states its paper-letter upper bound. -/
  s3014 : ℝ
  n : ℕ
  hl : 5 ≤ l
  hn : 2 ≤ n
  hl_eq : l = 2 * (n : ℝ) + 1
  hQ : 0 ≤ Q
  hM : M = Q / (2 * l)
  hlogDK : 0 ≤ logDK
  hlogSQ : 0 ≤ logSQ
  hlstar : 0 ≤ lstar
  /-- hii: Step (ii) final display (IUT IV L1424-1433) -/
  hii : (1 + 4 / l) * logDK ≤ (1 + 4 / l) * S_ar + 2 * Real.log l + 46
  /-- hsQ: the s^Q estimate (IUT IV L1570-1575) -/
  hsQ : (4 / l) * logSQ ≤ (8 * d_mod / l) * S_ar + 6
  /-- S_ar >= 0 (effective divisor degrees) -/
  hS_ar : 0 ≤ S_ar
  /-- d_mod >= 1 (IUT IV L1262) -/
  hd_mod : 1 ≤ d_mod
  /-- hvii: Step (vii) archimedean container bound (IUT IV lines 1819-1859) -/
  hvii : arch ≤ (l + 5) / 4 * Real.log Real.pi

/-- hviProcession (PROVED from the DONE StepV chain): the procession-normalized
average of the collection bounds is at most the paper's kappa-bracket
(IUT IV L1764-1783). -/
theorem hviProcession {ι : Type*} [Fintype ι] (P : PaperStepVIIIRetained ι) :
    (1 / (P.n : ℝ)) * (∑ j ∈ Finset.Icc 1 P.n,
        LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
          (2 * (P.n : ℝ) + 1) P.logDK P.Q P.logSQ P.lstar j)
      ≤ kappa P.l * ((1 + 4 / P.l) * P.logDK - (1 / 6) * P.Q
          + (4 / P.l) * P.logSQ + (20 / 3) * P.lstar) := by
  have h := p6_stepVAverages_ivInequality P.n P.hn P.logDK P.Q P.logSQ P.lstar
    P.hlogDK P.hlogSQ P.hlstar
  rw [P.hl_eq]
  have e : kappa (2 * (P.n : ℝ) + 1)
        * ((1 + 4 / (2 * (P.n : ℝ) + 1)) * P.logDK - (1 / 6) * P.Q
            + (4 / (2 * (P.n : ℝ) + 1)) * P.logSQ + (20 / 3) * P.lstar)
      = ((2 * (P.n : ℝ) + 1) + 1) / 4
        * ((1 + 4 / (2 * (P.n : ℝ) + 1)) * P.logDK - P.Q / 6
            + 4 / (2 * (P.n : ℝ) + 1) * P.logSQ + 20 / 3 * P.lstar) := by
    unfold kappa
    ring
  rw [e]
  exact h

/-- **hiii from the two primitive paper estimates** (narrowing of the Step (iii)
combined display into its two upstream retained pieces):
* hii: Step (ii) final display, IUT IV L1424-1433:
  (1 + 4/l) log(dK) <= (1 + 4/l) S_ar + 2 log l + 46;
* hsQ: the s^Q estimate, IUT IV L1570-1575:
  (4/l) log(s^Q) <= (8 d_mod/l) S_ar + 6;
with the paper facts S_ar >= 0 (effective divisor degrees) and d_mod >= 1 (L1262).
PROVED: hii + hsQ imply hiii. -/
theorem hiii_of_stepII_and_sQ {l S_ar d_mod logDK logSQ : ℝ}
    (hl : 0 < l) (hS : 0 ≤ S_ar) (hd : 1 ≤ d_mod)
    (hii : (1 + 4 / l) * logDK ≤ (1 + 4 / l) * S_ar + 2 * Real.log l + 46)
    (hsQ : (4 / l) * logSQ ≤ (8 * d_mod / l) * S_ar + 6) :
    (1 + 4 / l) * logDK + (4 / l) * logSQ
      ≤ (1 + 12 * d_mod / l) * S_ar + 2 * Real.log l + 52 := by
  have hl0 : 0 ≤ (4 : ℝ) := by norm_num
  have hcoef : 4 / l + 8 * d_mod / l ≤ 12 * d_mod / l := by
    have h4 : (4 : ℝ) ≤ 4 * d_mod := by linarith
    have hle : 4 / l ≤ 4 * d_mod / l := div_le_div_of_nonneg_right h4 (le_of_lt hl)
    have heq : 12 * d_mod / l = 4 * d_mod / l + 8 * d_mod / l := by ring
    rw [heq]
    linarith
  have hmain : (1 + 4 / l) * logDK + (4 / l) * logSQ
      ≤ (1 + 4 / l) * S_ar + 2 * Real.log l + 46 + ((8 * d_mod / l) * S_ar + 6) :=
    by linarith
  have hR : (1 + 4 / l) * S_ar + 2 * Real.log l + 46 + ((8 * d_mod / l) * S_ar + 6)
      ≤ (1 + 12 * d_mod / l) * S_ar + 2 * Real.log l + 52 := by
    nlinarith [hS, hcoef]
  linarith

/-- **Step (viii) assembly (pure algebra).**  The three retained paper
intermediates imply the paper's Step (viii) display in the exact form of the
hstepVIII consumed by uc_c3_paperConstants. -/

theorem hstepVIII_of_retained {ι : Type*} [Fintype ι] (P : PaperStepVIIIRetained ι)
    (w B : ι → ℝ) (hB : (∑ i, w i * B i) = P.s3014)
    (hlogP_le_logSQ : P.logP ≤ P.logSQ)
    (hviTable : P.s3014
      ≤ (1 / (P.n : ℝ)) * (∑ j ∈ Finset.Icc 1 P.n,
          LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
            (2 * (P.n : ℝ) + 1) P.logDK P.Q P.logP P.lstar j) + P.arch) :
    (∑ i, w i * B i) ≤
      kappa P.l * ((1 + 12 * P.d_mod / P.l) * P.S_ar + 2 * Real.log P.l + 56
        - cL P.l * P.Q + (20 / 3) * P.lstar) - P.M := by
  rw [hB]
  have hlpos : 0 < P.l := by linarith [P.hl]
  have hiii : (1 + 4 / P.l) * P.logDK + (4 / P.l) * P.logSQ
      ≤ (1 + 12 * P.d_mod / P.l) * P.S_ar + 2 * Real.log P.l + 52 :=
    hiii_of_stepII_and_sQ hlpos P.hS_ar P.hd_mod P.hii P.hsQ
  have hk : 0 < kappa P.l := by unfold kappa; linarith
  -- Step (vii): arch <= kappa l * 4
  have harch2 : P.arch ≤ kappa P.l * 4 := by
    have h2 : (P.l + 5) / 4 * Real.log Real.pi ≤ (P.l + 1) / 4 * 4 :=
      arch_container_le P.hl
    have e : kappa P.l * 4 = (P.l + 1) / 4 * 4 := by unfold kappa; ring
    linarith [P.hvii, h2, e]
  have hproc := hviProcession P
  -- monotone bridge: replacing the donor S slot logP by logSQ (hlogP_le_logSQ)
  have hmono : (1 / (P.n : ℝ)) * (∑ j ∈ Finset.Icc 1 P.n,
        LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
          (2 * (P.n : ℝ) + 1) P.logDK P.Q P.logP P.lstar j)
      ≤ (1 / (P.n : ℝ)) * (∑ j ∈ Finset.Icc 1 P.n,
        LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
          (2 * (P.n : ℝ) + 1) P.logDK P.Q P.logSQ P.lstar j) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro j _
    unfold LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
    linarith [hlogP_le_logSQ]
  have hviNew : P.s3014
      ≤ kappa P.l * ((1 + 4 / P.l) * P.logDK - (1 / 6) * P.Q
          + (4 / P.l) * P.logSQ + (20 / 3) * P.lstar) + P.arch := by
    linarith [hviTable, hmono, hproc]
  -- distribute the kappa-bracket
  have hviD : P.s3014 ≤
      kappa P.l * ((1 + 4 / P.l) * P.logDK) + kappa P.l * ((4 / P.l) * P.logSQ)
        + kappa P.l * ((20 / 3) * P.lstar) - kappa P.l * (1 / 6) * P.Q + P.arch := by
    calc P.s3014
        ≤ kappa P.l * ((1 + 4 / P.l) * P.logDK - (1 / 6) * P.Q + (4 / P.l) * P.logSQ
            + (20 / 3) * P.lstar) + P.arch := hviNew
      _ = kappa P.l * ((1 + 4 / P.l) * P.logDK) + kappa P.l * ((4 / P.l) * P.logSQ)
            + kappa P.l * ((20 / 3) * P.lstar) - kappa P.l * (1 / 6) * P.Q + P.arch := by
          ring
  -- Step (iii) weighted by kappa l > 0, distributed
  have hiiiD : kappa P.l * ((1 + 4 / P.l) * P.logDK) + kappa P.l * ((4 / P.l) * P.logSQ)
      ≤ kappa P.l * ((1 + 12 * P.d_mod / P.l) * P.S_ar + 2 * Real.log P.l + 52) := by
    calc kappa P.l * ((1 + 4 / P.l) * P.logDK) + kappa P.l * ((4 / P.l) * P.logSQ)
        = kappa P.l * ((1 + 4 / P.l) * P.logDK + (4 / P.l) * P.logSQ) := by ring
      _ ≤ kappa P.l * ((1 + 12 * P.d_mod / P.l) * P.S_ar + 2 * Real.log P.l + 52) :=
          mul_le_mul_of_nonneg_left hiii hk.le
  -- combine Steps (v)-(vii) into the "+56" bracket
  have hstep : P.s3014 ≤
      kappa P.l * ((1 + 12 * P.d_mod / P.l) * P.S_ar + 2 * Real.log P.l + 56
          + (20 / 3) * P.lstar) - kappa P.l * (1 / 6) * P.Q := by
    have e : kappa P.l * ((1 + 12 * P.d_mod / P.l) * P.S_ar + 2 * Real.log P.l + 52)
          + kappa P.l * ((20 / 3) * P.lstar) + kappa P.l * 4
        = kappa P.l * ((1 + 12 * P.d_mod / P.l) * P.S_ar + 2 * Real.log P.l + 56
            + (20 / 3) * P.lstar) := by
      ring
    linarith [hviD, hiiiD, harch2, e]
  -- final absorption: the paper's (l+1)/4 * (1/6) * (12/l^2) >= 1/(2l)
  have hgap : 0 ≤ kappa P.l * (1 / 6) * (12 / P.l ^ 2) * P.Q - P.M := by
    have hid : kappa P.l * (1 / 6) * (12 / P.l ^ 2) = (P.l + 1) / (2 * P.l ^ 2) := by
      unfold kappa
      field_simp
      ring
    have hdiff : 0 ≤ (P.l + 1) / (2 * P.l ^ 2) - 1 / (2 * P.l) := by
      have e : (P.l + 1) / (2 * P.l ^ 2) - 1 / (2 * P.l) = 1 / (2 * P.l ^ 2) := by
        field_simp
        ring
      rw [e]
      positivity
    rw [P.hM]
    rw [hid]
    have hm : 0 ≤ P.Q * ((P.l + 1) / (2 * P.l ^ 2) - 1 / (2 * P.l)) :=
      mul_nonneg P.hQ hdiff
    have heq : P.Q * ((P.l + 1) / (2 * P.l ^ 2) - 1 / (2 * P.l))
        = (P.l + 1) / (2 * P.l ^ 2) * P.Q - P.Q / (2 * P.l) := by ring
    linarith [hm, heq]
  -- rewrite target as intermediate minus kappa*(1/6)Q plus nonnegative gap
  have key : kappa P.l * ((1 + 12 * P.d_mod / P.l) * P.S_ar + 2 * Real.log P.l + 56
        - cL P.l * P.Q + (20 / 3) * P.lstar) - P.M
      = kappa P.l * ((1 + 12 * P.d_mod / P.l) * P.S_ar + 2 * Real.log P.l + 56
          + (20 / 3) * P.lstar) - kappa P.l * (1 / 6) * P.Q
        + (kappa P.l * (1 / 6) * (12 / P.l ^ 2) * P.Q - P.M) := by
    unfold cL
    field_simp
    ring
  rw [key]
  linarith [hstep, hgap]

#print axioms log_pi_le_two
#print axioms arch_container_le
#print axioms hviProcession
#print axioms hstepVIII_of_retained


open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1ActualHullTargetMagnitudeActual

/- ## The proved S-slot bridge (kurt ur_badWeightedLogP_le) -/

/-- PROVED (from kurt's Mzk1URSmallPrimeActual.ur_badWeightedLogP_le): with the
structure's logP := sum_b gamma_b * Real.log (qVFamTensorP T b) and logSQ :=
(sum_b gamma_b) * Real.log (urSQ X), the retained bridge hlogP_le_logSQ holds as
soon as every bad modulus is in the paper small-prime cutoff (hX : forall b,
qVFamTensorP T b <= X).  Provenance for hX: IUT IV small-prime set definition
(bad places lie in the small primes <= e*_mod * l). -/
theorem logP_aggregate_le_logSQ {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l) [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (X : ℕ) (hX : ∀ b : Bad (nativePlaceSelection T),
      LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual.qVFamTensorP T b ≤ X) :
    (∑ b : Bad (nativePlaceSelection T),
        LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T b
          * Real.log
            (LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual.qVFamTensorP T b : ℝ))
      ≤ (∑ b : Bad (nativePlaceSelection T),
          LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T b)
        * Real.log
          (LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual.urSQ X : ℝ) :=
  LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual.ur_badWeightedLogP_le (l := l) T X hX

/- ## hstepVIII from the collection layer (david hviTable_final + kurt bridge) -/

/-- **hstepVIII_of_collectionLayer**: instantiate PaperStepVIIIRetained from the
collection layer.  The hviTable field is DISCHARGED by david's proved
hviTable_final (Mzk1ULHviTableFinalActual), arch := 0 (hvii by positivity), the
S-slot bridge by kurt's logP_aggregate_le_logSQ with hX, and the aggregation
equalities are definitional.  Retained inputs: hX (small-prime cutoff), hiii (the
Step (iii) display) and hvii (reduced to 0 <= (l+5)/4 log pi, proved here). -/
theorem hstepVIII_of_collectionLayer {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l) [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (X : ℕ) (hX : ∀ b : Bad (nativePlaceSelection T),
      LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual.qVFamTensorP T b ≤ X)
    (n : ℕ) (hn : 2 ≤ n) (hl_eq : (l.value : ℝ) = 2 * (n : ℝ) + 1)
    (S_ar M d_mod : ℝ) (hl : 5 ≤ (l.value : ℝ))
    (D Q T' logP : Bad (nativePlaceSelection T) → ℝ)
    (Vh : Bad (nativePlaceSelection T) → ℕ → ℝ)
    (hlogP : ∀ b, logP b
      = Real.log
          (LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual.qVFamTensorP T b : ℝ))
    (hVh : ∀ i, ∀ label ∈ Finset.Icc 1 n,
      Vh i label ≤ LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
        (2 * (n : ℝ) + 1) (D i) (Q i) (logP i) (T' i) label)
    (hM : M = (∑ i : Bad (nativePlaceSelection T),
        LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i * Q i)
      / (2 * (l.value : ℝ)))
    (hD0 : ∀ i, 0 ≤ D i) (hQ0 : ∀ i, 0 ≤ Q i) (hT0 : ∀ i, 0 ≤ T' i)
    (hii : (1 + 4 / (l.value : ℝ)) *
          (∑ i : Bad (nativePlaceSelection T),
            LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i * D i)
        ≤ (1 + 4 / (l.value : ℝ)) * S_ar + 2 * Real.log (l.value : ℝ) + 46)
    (hsQ : (4 / (l.value : ℝ)) *
          ((∑ i : Bad (nativePlaceSelection T),
            LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i)
            * Real.log (LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual.urSQ X : ℝ))
        ≤ (8 * d_mod / (l.value : ℝ)) * S_ar + 6)
    (hS_ar : 0 ≤ S_ar) (hd_mod : 1 ≤ d_mod) :
    (∑ i : Bad (nativePlaceSelection T),
        LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i
          * ((1 / (n : ℝ)) * (∑ label ∈ Finset.Icc 1 n, Vh i label)))
      ≤ kappa (l.value : ℝ) * ((1 + 12 * d_mod / (l.value : ℝ)) * S_ar
          + 2 * Real.log (l.value : ℝ) + 56
          - cL (l.value : ℝ) *
            (∑ i : Bad (nativePlaceSelection T),
              LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i * Q i)
          + (20 / 3) *
            (∑ i : Bad (nativePlaceSelection T),
              LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i * T' i))
        - M := by
  classical
  have hγ0 : ∀ i, 0 ≤ LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i :=
    fun i => actualTargetWeight_nonneg (l := l) T i
  have hQ : 0 ≤ ∑ i : Bad (nativePlaceSelection T),
      LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i * Q i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hγ0 i) (hQ0 i))
  have hlogDK : 0 ≤ ∑ i : Bad (nativePlaceSelection T),
      LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i * D i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hγ0 i) (hD0 i))
  have hlstar : 0 ≤ ∑ i : Bad (nativePlaceSelection T),
      LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i * T' i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hγ0 i) (hT0 i))
  have hlogSQ : 0 ≤ (∑ i : Bad (nativePlaceSelection T),
        LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i)
      * Real.log (LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual.urSQ X : ℝ) := by
    have hγsum : 0 ≤ ∑ i : Bad (nativePlaceSelection T),
        LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i :=
      Finset.sum_nonneg (fun i _ => hγ0 i)
    have hX1 : (1 : ℝ) ≤ (LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual.urSQ X : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt
        (LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual.urSQ_pos X)
    exact mul_nonneg hγsum (Real.log_nonneg hX1)
  have hlogP_le : (∑ i : Bad (nativePlaceSelection T),
        LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i * logP i)
      ≤ (∑ i : Bad (nativePlaceSelection T),
          LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i)
        * Real.log
          (LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual.urSQ X : ℝ) := by
    have h := logP_aggregate_le_logSQ
      (l := l) T X hX
    calc (∑ i : Bad (nativePlaceSelection T),
          LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i * logP i)
        = ∑ i : Bad (nativePlaceSelection T),
            LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i
              * Real.log
                (LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual.qVFamTensorP T i : ℝ) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hlogP i]
      _ ≤ _ := h
  have hviT := LeanFormal.IUT.XiFPaper.Mzk1ULHviTableFinalActual.hviTable_final
    (b := Bad (nativePlaceSelection T))
    (fun i => LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i)
    hγ0 n hn logP D Q T' Vh hVh
  refine hstepVIII_of_retained
    ({ l := (l.value : ℝ), S_ar := S_ar,
       Q := (∑ i : Bad (nativePlaceSelection T),
          LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i * Q i),
       M := M, d_mod := d_mod,
       lstar := (∑ i : Bad (nativePlaceSelection T),
          LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i * T' i),
       logDK := (∑ i : Bad (nativePlaceSelection T),
          LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i * D i),
       logSQ := (∑ i : Bad (nativePlaceSelection T),
          LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i)
          * Real.log (LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual.urSQ X : ℝ),
       logP := (∑ i : Bad (nativePlaceSelection T),
          LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i * logP i),
       arch := 0,
       s3014 := (∑ i : Bad (nativePlaceSelection T),
          LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i
            * ((1 / (n : ℝ)) * (∑ label ∈ Finset.Icc 1 n, Vh i label))),
       n := n, hl := hl, hn := hn, hl_eq := hl_eq, hQ := hQ, hM := hM,
       hlogDK := hlogDK, hlogSQ := hlogSQ, hlstar := hlstar,
       hii := hii, hsQ := hsQ, hS_ar := hS_ar, hd_mod := hd_mod,
       hvii := by
         have hpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
         have : (0 : ℝ) ≤ ((l.value : ℝ) + 5) / 4 := by positivity
         positivity } :
      PaperStepVIIIRetained (Bad (nativePlaceSelection T)))
    (fun i => LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i)
    (fun i => (1 / (n : ℝ)) * (∑ label ∈ Finset.Icc 1 n, Vh i label))
    rfl hlogP_le (by simpa using hviT)

/- ## Audit record: our gamma-aggregation vs the paper lambda_e weighted average -/

/-- (i) DEFINITIONAL/PROVABLE: the sum of the native weights is the sum of the
inverse completion degrees (no normalization). -/
theorem nativeWeightsSum_eq_invDegreeSum {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l) [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)] :
    (∑ b : Bad (nativePlaceSelection T),
        LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T b)
      = ∑ b : Bad (nativePlaceSelection T),
          ((LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual.localCompletionDegree
            T.arithmetic
            (LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadToKPlace T b) : Nat) : ℝ)⁻¹ := by
  apply Finset.sum_congr rfl
  intro b _
  exact actualTargetWeight_eq_inv (l := l) T b

/-- AUDIT RECORD (Lead 2026-11-17 ruling (c), item (2)): the two weight families.

This is a named RECORD, not a proof of any equality between them:
(i) our gamma-aggregation is the nativeBadLocalWeight sum (definitional, see
    nativeWeightsSum_eq_invDegreeSum);
(ii) the paper lambda_e := [(F_mod)_v : Q_{vQ}] (IUT IV L1715-1716) with weighted
    average normalization sum_e lambda_e = d_mod (L1736-1741); d_mod appears in
    the final display coefficients (1+12 d_mod/l) and in the estimate
    log(s^Q) <= 2 d_mod S_ar + 5 + log l (L1569-1571, L1866-1878);
(iii) our c := sum_b nativeBadLocalWeight = sum_{v in V_bad(F_mod)}
    1/[K_{w(v)}:F_v] (exact inverse-degree expression, INDEPENDENT of d_mod; no
    degree-sum identity for inverse degrees exists -- the valid one is
    sum_{w|v} e_w f_w = [K:F_v]).
NOTE (kurt 2026-11-17, Mzk1URBadWeightSumActual): NEITHER c = d_mod NOR c = 1 is
provable from the tree: d_mod is only a paper parameter (ExplicitConstantObject.dmod,
with Mzk1Stage4HeightRegionNumericsActual.dMod := 1 a placeholder) and there is no
relation theorem; kurt keeps c = d_mod as the named condition BadWeightTotalEqDmod.
Our aggregation does NOT need either equality (Lead ruling).
The two families differ in general; a conversion layer (if H-T ever needs the
strict paper lambda/d_mod weighting on the LHS) is a separate NEW task. -/
structure NativeVsPaperWeightsRecord (l : PrimeGeFive)
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)] where
  /-- paper local degrees lambda_e = [(F_mod)_v : Q_{vQ}] (IUT IV L1715-1716) -/
  lam : Bad (nativePlaceSelection T) → ℝ
  /-- d_mod = [F_mod : Q] -/
  d_mod : ℝ
  /-- paper weighted-average normalization: sum_e lambda_e = d_mod (L1736-1741) -/
  paper_lambda_sum : (∑ b, lam b) = d_mod
  /-- lambda_e in R_{>0} (L1715-1716) -/
  hlam_pos : ∀ b, 0 < lam b
  /-- our aggregate c := sum_b nativeBadLocalWeight (the gamma-aggregation constant) -/
  c : ℝ
  /-- definitional link to our weights -/
  hc_def : c = ∑ b, LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T b

/-! ## U-C C4 with htheta as a named retained condition -/

/-- **U-C C4 closure with the retained conditions named.**  Inputs:
* hscale / hpacket: the named retained U-R root-extension-to-tensor transport
  conditions (RootHullScalingFormulaAt and the per-b numerical packet comparison),
  supplying htheta = actualThetaHullLogRoot <= ucWeightedHpkt (nativeBadLocalWeight T) V
  through Mzk1URThetaHthetaActual.ur_htheta_of_scaling;
* hstepVIII: the retained Step (viii) display (this file's PaperStepVIIIRetained
  yields exactly this shape, see hstepVIII_of_retained), with lstar instantiated at
  the actual paperLstarLogs;
* the actual U-C C3/C4 machinery (uc_c4_paperConstants_of_p6) closes the sandwich.
No other arithmetic assumptions are used. -/
theorem uc_c4_of_retained {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (V B : Bad (nativePlaceSelection T) → ℝ)
    (hscale : ∀ b : Bad (nativePlaceSelection T),
      LeanFormal.IUT.XiFPaper.BadPlaceThetaHullCorrectionFormulaActual.RootHullScalingFormulaAt
        (l := l) T b)
    (hpacket : ∀ b : Bad (nativePlaceSelection T),
      -LeanFormal.IUT.XiFPaper.BadPlaceThetaHullCorrectionFormulaActual.thetaCoefficientContribution
        (l := l) T b ≤ V b)
    (hVB : ∀ b : Bad (nativePlaceSelection T), V b ≤ B b)
    {η0 : ℝ} (hη0 : 0 < η0)
    (hπ : ∀ η : ℝ, η0 ≤ η →
      (Nat.primeCounting ⌊η⌋₊ : ℝ) ≤ 4 * η / (3 * Real.log η))
    {eMod : Nat} (he : 1 ≤ eMod)
    (eta_prm S_ar Q d_mod : ℝ) (hl : 5 ≤ (l.value : ℝ)) (heta : η0 ≤ eta_prm)
    (hstepVIII :
      (∑ i : Bad (nativePlaceSelection T),
          LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i * B i) ≤
        kappa (l.value : ℝ) * ((1 + 12 * d_mod / (l.value : ℝ)) * S_ar
          + 2 * Real.log (l.value : ℝ) + 56
          - cL (l.value : ℝ) * Q
          + (20 / 3) * Mzk1ULHpktActual.paperLstarLogs eMod (l.value : ℝ))
          - actualQPilotMagnitudeClassical (l := l) T) :
    cL (l.value : ℝ) * Q ≤ Mzk1ULHpktActual.paperA d_mod (l.value : ℝ) S_ar
      (Mzk1ULHpktActual.paperEar eMod (l.value : ℝ) eta_prm) := by
  classical
  have htheta :=
    LeanFormal.IUT.XiFPaper.Mzk1URThetaHthetaActual.ur_htheta_of_scaling
      (l := l) T hscale V hpacket
  exact LeanFormal.IUT.XiFPaper.Mzk1UCHpktActual.uc_c4_paperConstants_of_p6 (l := l) T
    (LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T) V B
    (fun b => LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual.actualTargetWeight_nonneg (l := l) T b)
    hVB hη0 hπ he eta_prm S_ar Q d_mod hl heta htheta hstepVIII

#print axioms nativeWeightsSum_eq_invDegreeSum
#print axioms logP_aggregate_le_logSQ
#print axioms hstepVIII_of_collectionLayer
#print axioms uc_c4_of_retained



/-- **de-conditionalized Step(viii)**: actual paper letters.  S_ar := SAr_tripodal T
(/finrank normalized, proved nonnegative), d_mod := dMod T (proved >= 1); the
Step (ii) and s^Q letter inputs are DISCHARGED by david's proved pure-real
lemmas hii_arith/hsQ_arith from the two actual letter inequalities hlogdK/hsQraw. -/
theorem hstepVIII_of_paperLetters {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l) [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (X : ℕ) (hX : ∀ b : Bad (nativePlaceSelection T),
      LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual.qVFamTensorP T b ≤ X)
    (n : ℕ) (hn : 2 ≤ n) (hl_eq : (l.value : ℝ) = 2 * (n : ℝ) + 1)
    (M : ℝ) (hl : 5 ≤ (l.value : ℝ))
    (D Q T' logP : Bad (nativePlaceSelection T) → ℝ)
    (Vh : Bad (nativePlaceSelection T) → ℕ → ℝ)
    (hlogP : ∀ b, logP b
      = Real.log
          (LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual.qVFamTensorP T b : ℝ))
    (hVh : ∀ i, ∀ label ∈ Finset.Icc 1 n,
      Vh i label ≤ LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
        (2 * (n : ℝ) + 1) (D i) (Q i) (logP i) (T' i) label)
    (hM : M = (∑ i : Bad (nativePlaceSelection T),
        LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i * Q i)
      / (2 * (l.value : ℝ)))
    (hD0 : ∀ i, 0 ≤ D i) (hQ0 : ∀ i, 0 ≤ Q i) (hT0 : ∀ i, 0 ≤ T' i)
    (hlogdK : (∑ i : Bad (nativePlaceSelection T),
        LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i * D i)
      ≤ LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual.SAr_tripodal T
        + 2 * Real.log (l.value : ℝ) + 21)
    (hsQraw : (∑ i : Bad (nativePlaceSelection T),
        LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i)
        * Real.log (LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual.urSQ X : ℝ)
      ≤ 2 * (LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual.dMod T)
          * LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual.SAr_tripodal T
        + 5 + Real.log (l.value : ℝ)) :
    (∑ i : Bad (nativePlaceSelection T),
        LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i
          * ((1 / (n : ℝ)) * (∑ label ∈ Finset.Icc 1 n, Vh i label)))
      ≤ kappa (l.value : ℝ) * ((1 + 12 * LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual.dMod T
            / (l.value : ℝ))
          * LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual.SAr_tripodal T
          + 2 * Real.log (l.value : ℝ) + 56
          - cL (l.value : ℝ) *
            (∑ i : Bad (nativePlaceSelection T),
              LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i * Q i)
          + (20 / 3) *
            (∑ i : Bad (nativePlaceSelection T),
              LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i * T' i))
        - M := by
  have hii := LeanFormal.IUT.XiFPaper.Mzk1ULStepHiiHsQActual.hii_arith hl hlogdK
  have hsQ := LeanFormal.IUT.XiFPaper.Mzk1ULStepHiiHsQActual.hsQ_arith hl hsQraw
  exact hstepVIII_of_collectionLayer (l := l) T X hX n hn hl_eq
    (LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual.SAr_tripodal T) M
    (LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual.dMod T) hl D Q T' logP Vh
    hlogP hVh hM hD0 hQ0 hT0 hii hsQ
    (LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual.zero_le_SAr_tripodal T)
    (LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual.one_le_dMod T)

/- WEIGHT CONVENTION (Lead ruling 2026-11-17, paper IUT IV L977-1000, L1045-1102):
the OUTER weight of the Step(viii)/C4 chain is `normDegreeWeight = f_P/[K:Q]`
(fiber-normalized E-degree; outer sum over v_Q accumulates the denominator to
[F:Q]).  `nativeBadLocalWeight = 1/[K_w:F_v]` (the gamma family) is SUPERSEDED
for the C4/U-L main chain: it is retained only in legacy F-side U-R objects and
in the Step(v) inner lambda-average slot (paperWeight), and must not be used as
the outer weight of hstepVIII / hii / the D-slot letters.  Code below is kept
unchanged for backward compatibility; call sites migrating to K-side letters
pass normDegreeWeight (Mzk1ULSideWeightBridgeActual / Mzk1ULKSideCountActual).
-/
end LeanFormal.IUT.XiFPaper.Mzk1ULStepVIIIActual
end