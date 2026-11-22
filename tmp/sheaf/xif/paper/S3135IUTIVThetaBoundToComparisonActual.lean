import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontier
import LeanFormal.IUT.ABCBridge.Geometry.ABCModelHeightComparison

/-!
# IUT IV Theorem 1.10 `C_Θ >= -1` → the height/weight comparison

This file formalizes the real-variable bookkeeping of IUT IV Theorem 1.10
(`:1255-1385`) and the section 2 passage to the ABC height/weight bound, on
source-realized quantities:

* `log q` (`IUT IV:1302-1362`) is realized as the logarithmic height of the actual
  rational Frey `j`-invariant (`ABCModelHeightComparison.lean:78-105`); on the bad
  support the actual q-parameter is `q = j^{-1}`
  (`ABCModelHeightComparison.lean:257-264`), and `|log q| = log(q)/(2l)`
  (`IUT IV:1358-1362`).
* `log d_F + log f_F` is the paper's log-different + log-conductor sum
  (`IUT IV:1297-1351`); over the lambda-line rational points this is the section-2
  quantity `log-diff + log-cond`, whose actual dictionary value is the arithmetic
  weight (proved in `S3135LambdaLineHeightLogCondActual.lean`).
* the theta-pilot hull log-volume `-|log Θ|` upper computation of
  `IUT IV:1363-1376` (the `C_Θ` formula) is the named input
  `IUTIVThetaHullComputation`;
* the Corollary 3.12 lower bound `-|log Θ| >= -|log q|` (`IUT III:10324-10353`),
  i.e. `C_Θ >= -1`, is the named input `IUTIVCor312LowerBound`; it is the
  source-realized form of the Batch A comparison `Q_C <= H_C`
  (`S3130QCLeHCActual.S3130QCLeHCGap`).

## What is proved

`s3135_display_of_cor312_thetaComputation`: from the two named inputs, the initial
data bound `log q <= l^2` (choice of `l ~ (log q)^{1/2}`, `Explicit estimates:123-126`)
and the arithmetic side conditions `l >= 5`, `d_mod >= 0`, `e*_mod >= 1`,
`η_prm >= 0`, `log-diff + log-cond >= 0`, the displayed estimate of
`IUT IV:1376-1385` follows:
`(1/6)·log q <= (1 + 20 d_mod/l)·(log d_F + log f_F) + 20(e*_mod l + η_prm)`.

`s3135_heightBound_of_display`: with the actual Frey model comparison
`6·ht(x) + log(27/64) <= h(j)` (`abcJInvariant_logHeight_bounds_abcRationalPoint`),
the display yields `ht(x) <= (1 + 20 d_mod/l)·W + 20(e*_mod l + η_prm) - log(27/64)/6`.

`s3135_ABCHeightWeightAdditiveBoundV2_of_paperInputs`: adding the section-2
uniformity passage (named `IUTIVSection2Uniformity`, the bounded-discrepancy
translation of Theorem A / [GenEll], `IUT IV:93-112`, `:2404-2430`), one gets the
version-2 additive height/arithmetic-weight contract `ABCHeightWeightAdditiveBoundV2`
— i.e. the second triangle of IUT IV section 2, conditional exactly on the two named
Theorem 1.10 inputs and the section-2 uniformity.

Nothing here asserts Theorem 1.10, Corollary 3.12, or ABC; the named inputs are
exposed, not hidden.
-/

noncomputable section

open scoped BigOperators NNReal ENNReal
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S3135IUTIVThetaBoundToComparisonActual

universe u

/-! ## 1. Source-realized paper quantities -/

/-- The realized `log q` of IUT IV:1302-1362: the logarithmic height of the actual
rational Frey `j`-invariant. -/
noncomputable def freyLogQ (a b c : ℕ) : ℝ :=
  Height.logHeight₁ (abcJInvariant a b c)

theorem freyLogQ_eq_logHeight_abcJInvariant (a b c : ℕ) :
    freyLogQ a b c = Height.logHeight₁ (abcJInvariant a b c) := rfl

theorem freyLogQ_nonneg (a b c : ℕ) : 0 ≤ freyLogQ a b c :=
  Height.zero_le_logHeight₁ _

/-- The realized q-pilot log-volume `Q_C = -|log q|` with `|log q| = log(q)/(2l)`
(IUT III:10340-10353; IUT IV:1358-1362). -/
noncomputable def qPilotLogVolume (l : ℝ) (a b c : ℕ) : ℝ :=
  -(freyLogQ a b c / (2 * l))

/-- The brace of the explicit `C_Θ` formula, IUT IV:1363-1376. -/
noncomputable def thetaHullBrace (l dmod emod eta W q : ℝ) : ℝ :=
  (1 + 12 * dmod / l) * W + 10 * (emod * l + eta) -
    (1 / 6) * (1 - 12 / l ^ 2) * q

/-- The explicit upper bound on the theta-pilot hull log-volume `-|log Θ|` from the
computation of IUT IV:1363-1376. -/
noncomputable def thetaHullUpper (l dmod emod eta W q : ℝ) : ℝ :=
  (l + 1) / 4 * thetaHullBrace l dmod emod eta W q - q / (2 * l)

/-! ## 2. Named source inputs -/

/-- **Corollary 3.12 lower bound (named input).**  `-|log Θ| >= -|log q|`, i.e.
`C_Θ >= -1` (IUT III:10324-10353), at the realized readouts; this is the
source-realized Batch A comparison `Q_C <= H_C` (`S3130QCLeHCGap`). -/
def IUTIVCor312LowerBound (l : ℝ) (HTheta : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ a b c : ℕ, IsABCTriple a b c → qPilotLogVolume l a b c ≤ HTheta a b c

/-- **Sign bridge for the Corollary 3.12 readout.**  The theta-pilot hull
log-volume is *signed*: `-|log Θ|`.  If the hull side were written as the
nonnegative magnitude `Hmag = |log Θ| >= 0`, the mixed comparison
`-|log q| <= Hmag` would be automatic (vacuous, see
`qPilotLogVolume_le_of_nonneg_magnitude`).  The contentful statement is the
signed comparison `-|log q| <= -Hmag`, equivalently the magnitude comparison
`Hmag <= |log q|`; this equivalence is recorded here so consumers cannot
silently use the vacuous form. -/
theorem iutivCor312LowerBound_signBridge (l : ℝ) (Hmag : ℕ → ℕ → ℕ → ℝ) :
    IUTIVCor312LowerBound l (fun a b c => -Hmag a b c) ↔
      ∀ a b c : ℕ, IsABCTriple a b c → Hmag a b c ≤ freyLogQ a b c / (2 * l) := by
  constructor
  · intro h a b c habc
    have h' := h a b c habc
    unfold qPilotLogVolume at h'
    linarith
  · intro h a b c habc
    have h' := h a b c habc
    unfold qPilotLogVolume
    linarith

/-- **Why the signed form matters.**  For a nonnegative hull magnitude the mixed
comparison `qPilotLogVolume l a b c <= Hmag a b c` is automatic: the signed
q-pilot log-volume is nonpositive.  Hence a Cor 3.12 input stated in this mixed
form carries no information. -/
theorem qPilotLogVolume_le_of_nonneg_magnitude (l : ℝ) (hl : 0 < l)
    {Hmag : ℕ → ℕ → ℕ → ℝ} (hHmag : ∀ a b c : ℕ, 0 ≤ Hmag a b c) :
    ∀ a b c : ℕ, IsABCTriple a b c → qPilotLogVolume l a b c ≤ Hmag a b c := by
  intro a b c _
  unfold qPilotLogVolume
  have hq : 0 ≤ freyLogQ a b c / (2 * l) :=
    div_nonneg (freyLogQ_nonneg a b c) (by linarith)
  have h := hHmag a b c
  linarith

/-- **Theta-pilot hull log-volume computation (named input).**  The estimate of
IUT IV:1363-1376 giving the explicit upper bound on the *signed* theta-pilot hull
log-volume `-|log Θ|` (the fourth-triangle hull computation), on source-realized
quantities: `HTheta = -|log Θ| <= (l+1)/4·brace - |log q|`, where `brace` is the
`C_Θ` brace of IV:1363-1376. -/
def IUTIVThetaHullComputation (l dmod emod eta : ℝ)
    (W : ℕ → ℕ → ℕ → ℝ) (HTheta : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ a b c : ℕ, IsABCTriple a b c →
    HTheta a b c ≤ thetaHullUpper l dmod emod eta (W a b c) (freyLogQ a b c)

/-- **The displayed estimate of IUT IV Theorem 1.10 (:1376-1385).** -/
def IUTIVTheorem110Display (l dmod emod eta : ℝ) (W : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ a b c : ℕ, IsABCTriple a b c →
    (1 / 6) * freyLogQ a b c ≤ (1 + 20 * dmod / l) * W a b c +
      20 * (emod * l + eta)

/-! ## 3. Real-variable bookkeeping -/

/-- Real-variable core of the passage from `C_Θ >= -1` (the brace being nonnegative)
to the display of IUT IV:1376-1385: the `12/l^2` term is absorbed by the bound
`log q <= l^2`, and the `20`-constants dominate the `12/10`-constants using
`l >= 5` and `e*_mod >= 1`. -/
theorem display_of_brace (l dmod emod eta W q : ℝ) (hl : 5 ≤ l) (hd : 0 ≤ dmod)
    (he : 1 ≤ emod) (heta : 0 ≤ eta) (hW : 0 ≤ W) (hq0 : 0 < q) (hql : q ≤ l ^ 2)
    (hbrace : 0 ≤ thetaHullBrace l dmod emod eta W q) :
    (1 / 6) * q ≤ (1 + 20 * dmod / l) * W + 20 * (emod * l + eta) := by
  have hl0 : (0 : ℝ) < l := by linarith
  unfold thetaHullBrace at hbrace
  have hA : (1 / 6) * (1 - 12 / l ^ 2) * q ≤
      (1 + 12 * dmod / l) * W + 10 * (emod * l + eta) := by linarith
  have hq2 : 2 * q / l ^ 2 ≤ 2 := by
    rw [div_le_iff₀ (pow_pos hl0 2)]
    nlinarith
  have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hl0)
  have hdecomp : (1 / 6) * q = (1 / 6) * (1 - 12 / l ^ 2) * q + 2 * q / l ^ 2 := by
    field_simp [hl2, ne_of_gt hl0]
    ring
  have hL : (1 / 6) * q ≤ (1 + 12 * dmod / l) * W + 10 * (emod * l + eta) + 2 := by
    linarith
  have h1 : 0 ≤ (dmod / l) * W :=
    mul_nonneg (div_nonneg hd (le_of_lt hl0)) hW
  have hel : (5 : ℝ) ≤ emod * l := by
    simpa using mul_le_mul he hl (by norm_num : (0 : ℝ) ≤ 5)
      (by linarith : (0 : ℝ) ≤ emod)
  have h2 : (2 : ℝ) ≤ 10 * (emod * l + eta) := by nlinarith
  have e1 : (1 + 20 * dmod / l) * W =
      (1 + 12 * dmod / l) * W + 8 * (dmod / l) * W := by ring
  have h3 : (1 + 12 * dmod / l) * W + 10 * (emod * l + eta) + 2 ≤
      (1 + 20 * dmod / l) * W + 20 * (emod * l + eta) := by
    rw [e1]
    nlinarith [h1, h2]
  linarith

/-- **The display of Theorem 1.10 from Corollary 3.12 + the theta-hull computation.**
Combining the two named source inputs at fixed paper data, the arithmetic side
conditions, the initial-data bound `log q <= l^2` and the positivity `log q > 0`,
yields the displayed estimate of IUT IV:1376-1385. -/
theorem s3135_display_of_cor312_thetaComputation
    (l dmod emod eta : ℝ) (hl : 5 ≤ l) (hd : 0 ≤ dmod) (he : 1 ≤ emod)
    (heta : 0 ≤ eta) {W : ℕ → ℕ → ℕ → ℝ} {HTheta : ℕ → ℕ → ℕ → ℝ}
    (hW : ∀ a b c : ℕ, 0 ≤ W a b c)
    (hBatchA : IUTIVCor312LowerBound l HTheta)
    (hTheta : IUTIVThetaHullComputation l dmod emod eta W HTheta)
    (hlogq_le : ∀ a b c : ℕ, IsABCTriple a b c → freyLogQ a b c ≤ l ^ 2)
    (hlogq_pos : ∀ a b c : ℕ, IsABCTriple a b c → 0 < freyLogQ a b c) :
    IUTIVTheorem110Display l dmod emod eta W := by
  intro a b c habc
  have hQ := hBatchA a b c habc
  have hU := hTheta a b c habc
  have hlpos : (0 : ℝ) < (l + 1) / 4 := by linarith
  have hprod : 0 ≤ (l + 1) / 4 *
      thetaHullBrace l dmod emod eta (W a b c) (freyLogQ a b c) := by
    unfold qPilotLogVolume at hQ
    unfold thetaHullUpper at hU
    linarith
  have hbrace : 0 ≤ thetaHullBrace l dmod emod eta (W a b c) (freyLogQ a b c) := by
    by_contra hneg
    push_neg at hneg
    exact absurd (mul_neg_of_pos_of_neg hlpos hneg) (not_lt.mpr hprod)
  exact display_of_brace l dmod emod eta (W a b c) (freyLogQ a b c) hl hd he heta
    (hW a b c) (hlogq_pos a b c habc) (hlogq_le a b c habc) hbrace

/-- **Height bound from the display.**  The actual Frey model comparison
`6·ht(x) + log(27/64) <= h(j) = log q`
(`abcJInvariant_logHeight_bounds_abcRationalPoint`) converts the display into
`ht(x) <= (1 + 20 d_mod/l)·W + 20(e*_mod l + η_prm) - log(27/64)/6`. -/
theorem s3135_heightBound_of_display (l dmod emod eta : ℝ) {W : ℕ → ℕ → ℕ → ℝ}
    (hdisp : IUTIVTheorem110Display l dmod emod eta W) :
    ∀ a b c : ℕ, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + 20 * dmod / l) * W a b c + 20 * (emod * l + eta) -
          Real.log (27 / 64 : ℝ) / 6 := by
  intro a b c habc
  have hd := hdisp a b c habc
  rw [freyLogQ_eq_logHeight_abcJInvariant a b c] at hd
  have h6 := (abcJInvariant_logHeight_bounds_abcRationalPoint habc).1
  linarith

/-! ## 4. The section-2 uniformity passage (named input) -/

/-- **Section-2 uniformity (named input, not proved).**  For every `eps > 0` one can
choose uniform initial-Θ-data constants `(l, d_mod, e*_mod, η_prm)` and a residual
constant `D`, and a source-realized `log-diff + log-cond` readout `W` equal to the
arithmetic weight, such that the Theorem 1.10 display holds with
`20 d_mod/l <= eps` and `20(e*_mod l + η_prm) <= D`.  This is the bounded-discrepancy
uniformity passage of IUT IV section 2 (Theorem A, IUT IV:93-112; [GenEll] section 1,
IUT IV:2404-2430, Remark 2.3.1): the constants of the initial data are controlled by
`log-diff + log-cond` uniformly over the compactly bounded family.  It is the exact
remaining section-2 input of the ABC specialization. -/
def IUTIVSection2Uniformity : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ (l dmod emod eta D : ℝ)
    (W : ℕ → ℕ → ℕ → ℝ),
    5 ≤ l ∧ 0 ≤ dmod ∧ 1 ≤ emod ∧ 0 ≤ eta ∧
      20 * dmod / l ≤ eps ∧ 20 * (emod * l + eta) ≤ D ∧
      (∀ a b c : ℕ, IsABCTriple a b c →
        W a b c = arithmeticWeight (abcRationalPoint a c)) ∧
      IUTIVTheorem110Display l dmod emod eta W

/-- **The second triangle of IUT IV section 2, conditional on the named inputs.**
From the section-2 uniformity passage (which contains the Theorem 1.10 display at
source-realized quantities) the version-2 additive height/arithmetic-weight contract
`ABCHeightWeightAdditiveBoundV2` follows.  This is the exact IUT IV section 2
implication; the named input is not proved here. -/
theorem s3135_ABCHeightWeightAdditiveBoundV2_of_paperInputs
    (hu : IUTIVSection2Uniformity) : ABCHeightWeightAdditiveBoundV2 := by
  intro eps heps
  obtain ⟨l, dmod, emod, eta, D, W, hl, hd, he, heta, hslope, hconst, hdict, hdisp⟩ :=
    hu eps heps
  refine ⟨D - Real.log (27 / 64 : ℝ) / 6, fun a b c habc => ?_⟩
  have hh := s3135_heightBound_of_display l dmod emod eta hdisp a b c habc
  rw [hdict a b c habc] at hh
  have hw : 0 ≤ arithmeticWeight (abcRationalPoint a c) := arithmeticWeight_nonneg _
  have hslope' : (20 * dmod / l) * arithmeticWeight (abcRationalPoint a c) ≤
      eps * arithmeticWeight (abcRationalPoint a c) :=
    mul_le_mul_of_nonneg_right hslope hw
  nlinarith [hh, hslope', hw, hconst]

#check IUTIVCor312LowerBound
#check IUTIVThetaHullComputation
#check s3135_display_of_cor312_thetaComputation
#check s3135_heightBound_of_display
#check s3135_ABCHeightWeightAdditiveBoundV2_of_paperInputs

end LeanFormal.IUT.XiFPaper.S3135IUTIVThetaBoundToComparisonActual
end
