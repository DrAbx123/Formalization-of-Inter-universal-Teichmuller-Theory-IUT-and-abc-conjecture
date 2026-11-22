/-
  # Log-volume of the source holomorphic hull (Corollary 3.12 candidate)

  This module proves, for the value-monoid realization of the source holomorphic hull
  of `SourceImageHull.lean`, the log-volume statements that the proof of IUT III
  Corollary 3.12 needs:

  * the log-volume of a global value point is the sum of the local log-degrees
    `log |deg_v|` over the finite index of processions and labels
    (`sourcePointVolume`), the paper's `μ_log` of Proposition 3.9, (i);
  * the point log-volume of an actual theta-pilot image is the index cardinality times
    the logarithm of the actual theta special value
    (`sourcePointVolume_thetaPilotPoint`), the value-realized form of the theta
    evaluation of Theorem 3.11, (i), (a);
  * the hull volume is at least the volume of the image union it contains
    (`sourceHullVolume_ge_imageVolume`), the monotonicity half of the paper's
    `P ⊆ φ(P)` estimate;
  * under the paper's compactness bound, both the Θ-pilot log-volume of the union of
    possible images (`sourceSetVolume_possibleImage_lt_top_of_compactBound`) and the
    log-volume of the holomorphic hull (`sourceHullVolume_lt_top_of_hullBound`) are
    finite.  This is the finiteness step of Corollary 3.12, conditional on the named
    compactness hypothesis;
  * the procession-normalized lower bound
    (`sourceSetVolume_possibleImage_ge_normalized`): the index cardinality times the
    `j ∈ F_l^⋇`-average of the actual theta values, Remark 3.1.1, (ii).
  * the paper-shaped scaled-unit-region reduction
    (`sourceHullVolume_lt_top_of_scaledRegionImage`): containment of the hull in a
    `λ`-multiple of a log-shell-bounded unit region yields finiteness of the hull
    volume, together with the normalized lower bound on the hull itself
    (`sourceHullVolume_ge_normalized`);
  * the proved failure of an internal bound: under the pointwise degree faithfulness
    under which the log-volume formulas above hold, the hull log-degree is unbounded
    above (`sourceHolomorphicHull_logDegree_unbounded`), the whole-hull bound
    hypothesis of the conditional finiteness is unsatisfiable
    (`not_exists_sourceHullLogDegreeBound_of_degreeFaithful`), and the value-realized
    hull volume is `⊤` (`sourceHullVolume_eq_top_of_degreeFaithful`).

  The paper derives *finiteness* of `−|log(Θ)|` from "the compactness of the
  `1,◦U_{j,vQ}`, together with the definition of the log-volume".  Compactness is not
  available from `OriginalInput`; it is recorded here as the named hypothesis
  `SourceCompactBound`, never as a promised field.  The unconditional finiteness
  assertion of Corollary 3.12 is therefore conditional at this level of realization,
  and the condition is stated explicitly.

  Source correspondence: IUT III, Remark 3.1.1, (ii), (iii), (iv); Proposition 3.9,
  (i), (ii); Corollary 3.12 statement and proof.
-/

import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe ua uv upi umon ui

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. The index of the source log-volume -/

/-- The index set of the source log-volume: procession `n` and label `j`. -/
abbrev SourceVolumeIndex (l : PrimeGeFive) : Type :=
  ThetaPilotCarrier l × SignedLabel l.value

instance sourceVolumeIndexFintype (l : PrimeGeFive) :
    Fintype (SourceVolumeIndex l) :=
  inferInstanceAs (Fintype (Fin (lStar l.value + 1) × SignedLabel l.value))

/-- The source volume index is equivalent to the product of `Fin` and the signed
labels, through which its cardinality is computed. -/
def sourceVolumeIndexEquiv (l : PrimeGeFive) :
    SourceVolumeIndex l ≃ (Fin (lStar l.value + 1) × SignedLabel l.value) :=
  (Equiv.Set.univ (SourceVolumeIndex l)).symm.trans
    (Equiv.Set.univ (Fin (lStar l.value + 1) × SignedLabel l.value))

/-- The cardinality of the source log-volume index. -/
theorem sourceVolumeIndex_finite (l : PrimeGeFive) :
    Fintype.card (SourceVolumeIndex l) = (lStar l.value + 1) * l.value := by
  rw [Fintype.card_congr (sourceVolumeIndexEquiv l)]
  rw [Fintype.card_prod, Fintype.card_fin, SignedLabel.card_signedLabel]

theorem sourceVolumeIndex_card_pos (l : PrimeGeFive) :
    0 < Fintype.card (SourceVolumeIndex l) := by
  rw [sourceVolumeIndex_finite]
  exact Nat.mul_pos (Nat.succ_pos _) l.prime.pos

/-! ## 2. The value-realized log-volume of a global value point -/

/-- The real log-degree of a global value point at the place `v`: the sum over the
finite index of the local `log |deg_v|`, computed with the actual degree homomorphism
of the source prime strip.  This is the paper's `μ_log` (Proposition 3.9, (i)) in the
value-monoid realization. -/
def sourceLocalLogDegree (v : V) (x : I.ThetaPilotPoint v) : Real :=
  ∑ i : SourceVolumeIndex l, I.logDegreeAt 0 0 v (x i)

/-- The log-volume of a global value point, as an extended nonnegative real. -/
def sourcePointVolume (v : V) (x : I.ThetaPilotPoint v) : ENNReal :=
  ENNReal.ofReal (I.sourceLocalLogDegree v x)

theorem sourceLocalLogDegree_one (v : V) :
    I.sourceLocalLogDegree v 1 = 0 := by
  unfold sourceLocalLogDegree
  simp [I.logDegreeAt_one]

theorem sourceLocalLogDegree_mul (v : V) (x y : I.ThetaPilotPoint v) :
    I.sourceLocalLogDegree v (x * y) =
      I.sourceLocalLogDegree v x + I.sourceLocalLogDegree v y := by
  unfold sourceLocalLogDegree
  rw [show (∑ i : SourceVolumeIndex l,
      I.logDegreeAt 0 0 v ((x * y) i)) =
      ∑ i : SourceVolumeIndex l,
        (I.logDegreeAt 0 0 v (x i) + I.logDegreeAt 0 0 v (y i)) from
    Finset.sum_congr rfl (fun i _ => I.logDegreeAt_mul 0 0 v (x i) (y i))]
  rw [Finset.sum_add_distrib]

/-- The log-degree of the realized `q`-parameter is the `q`-log: this is the
`degree_of_q` faithfulness field of the source realization. -/
theorem logDegreeAt_q (v : V) (R : I.SourceImageRealization v) :
    I.logDegreeAt 0 0 v
        (R.posRealAction (Multiplicative.ofAdd
          (Real.log ((I.theaterAt 0 0).thetaPacket.q)))) =
      Real.log ((I.theaterAt 0 0).thetaPacket.q) :=
  R.degree_of_q

/-- The log-degree of a global value point all of whose components equal the
realization of a single exponent. -/
theorem sourceLocalLogDegree_constant (v : V) (R : I.SourceImageRealization v)
    (a : Real)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    I.sourceLocalLogDegree v
      (I.constantThetaPilotPoint v R (Multiplicative.ofAdd a)) =
      (Fintype.card (SourceVolumeIndex l) : Real) * a := by
  unfold sourceLocalLogDegree
  simp only [I.constantThetaPilotPoint_apply]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hdeg a)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The unfolding of an actual source theta-pilot point as a constant global point. -/
theorem sourceThetaPilotPoint_eq_constant (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    I.sourceThetaPilotPoint v R n j =
      I.constantThetaPilotPoint v R
        (Multiplicative.ofAdd (Real.log (I.thetaValueAt (n.val : Int) 0 j))) :=
  rfl

/-- **Value-realized Θ-pilot log-volume.**  For the actual source theta special value
at procession `n` and label `j`, the realized log-degree of the theta-pilot point is
the index cardinality times `log` of that special value. -/
theorem sourceLocalLogDegree_thetaPilotPoint (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (j : SignedLabel l.value)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) =
      (Fintype.card (SourceVolumeIndex l) : Real) *
        Real.log (I.thetaValueAt (n.val : Int) 0 j) := by
  rw [I.sourceThetaPilotPoint_eq_constant v R n j]
  exact I.sourceLocalLogDegree_constant v R _ hdeg

/-- The point log-volume of an actual theta-pilot image point. -/
theorem sourcePointVolume_thetaPilotPoint (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (j : SignedLabel l.value)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    I.sourcePointVolume v (I.sourceThetaPilotPoint v R n j) =
      ENNReal.ofReal ((Fintype.card (SourceVolumeIndex l) : Real) *
        Real.log (I.thetaValueAt (n.val : Int) 0 j)) := by
  unfold sourcePointVolume
  rw [I.sourceLocalLogDegree_thetaPilotPoint v R n j hdeg]

/-! ## 3. The log-volume of subsets and of the hull -/

/-- The log-volume of a set of global value points: the supremum of the point
log-volumes.  This is the log-volume of a region as used in the proof of
Corollary 3.12. -/
def sourceSetVolume (v : V) (S : Set (I.ThetaPilotPoint v)) : ENNReal :=
  ⨆ x ∈ S, I.sourcePointVolume v x

/-- The log-volume of the source holomorphic hull of the union of possible
theta-pilot images at procession `n`. -/
def sourceHullVolume (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : ENNReal :=
  I.sourceSetVolume v (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))

theorem sourceSetVolume_mono (v : V) {S T : Set (I.ThetaPilotPoint v)}
    (hST : S ⊆ T) :
    I.sourceSetVolume v S ≤ I.sourceSetVolume v T := by
  refine iSup_le_iff.mpr ?_
  intro x
  refine iSup_le_iff.mpr ?_
  intro hx
  exact le_iSup_of_le x (le_iSup_of_le (hST hx) le_rfl)

/-- **Monotonicity estimate.**  The volume of the source hull is at least the volume
of the union of possible theta-pilot images, since the hull contains every image
point by construction. -/
theorem sourceHullVolume_ge_imageVolume (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) ≤
      I.sourceHullVolume v R n :=
  sourceSetVolume_mono (I := I) v
    (possibleThetaPilotImage_subset_sourceHolomorphicHull (I := I) v R n)

/-! ## 4. The Θ-pilot log-volume of the image union -/

/-- The log-volume of the union of possible theta-pilot images at procession `n`,
written as the supremum over the labels of the point log-volumes. -/
theorem sourceSetVolume_possibleImage_eq (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) =
      ⨆ (j : SignedLabel l.value),
        ENNReal.ofReal ((Fintype.card (SourceVolumeIndex l) : Real) *
          Real.log (I.thetaValueAt (n.val : Int) 0 j)) := by
  unfold sourceSetVolume
  refine le_antisymm ?_ ?_
  · refine iSup_le_iff.mpr ?_
    intro x
    refine iSup_le_iff.mpr ?_
    intro hx
    obtain ⟨j, rfl⟩ := (mem_possibleThetaPilotImageSet_iff (I := I) v R n x).mp hx
    rw [I.sourcePointVolume_thetaPilotPoint v R n j hdeg]
    exact le_iSup_of_le j le_rfl
  · refine iSup_le_iff.mpr ?_
    intro j
    refine le_iSup_of_le (I.sourceThetaPilotPoint v R n j) ?_
    refine le_iSup_of_le (I.sourceThetaPilotPoint_mem v R n j) ?_
    rw [I.sourcePointVolume_thetaPilotPoint v R n j hdeg]

/-- **Procession-normalized lower bound.**  The Θ-pilot log-volume of the image union
is at least the index cardinality times the log-volume of any one of the actual theta
special values; dividing by the cardinality gives the normalized (`j ∈ F_l^⋇`-averaged)
form of Remark 3.1.1, (ii). -/
theorem sourceSetVolume_possibleImage_ge_normalized (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    (j₀ : SignedLabel l.value) :
    ENNReal.ofReal ((Fintype.card (SourceVolumeIndex l) : Real) *
        Real.log (I.thetaValueAt (n.val : Int) 0 j₀)) ≤
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) := by
  rw [sourceSetVolume_possibleImage_eq (I := I) v R n hdeg]
  exact le_iSup_of_le j₀ le_rfl

/-! ## 5. The compactness hypothesis of the paper and the conditional finiteness -/

/-- The compactness bound of the proof of Corollary 3.12, at the value-monoid level:
the image union of the theta-pilot object is bounded in log-degree.  The paper obtains
this from the compactness of `1,◦U_{j,vQ}`; it is not available from `OriginalInput`,
so it is a named hypothesis and never a promised field. -/
def SourceCompactBound (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : Prop :=
  ∃ C : Real, ∀ j : SignedLabel l.value,
    (Fintype.card (SourceVolumeIndex l) : Real) *
      Real.log (I.thetaValueAt (n.val : Int) 0 j) ≤ C

/-- Under the paper's compactness bound, the log-volume of the union of possible
theta-pilot images is finite.  This is the "definition of the log-volume" half of the
finiteness argument of Corollary 3.12. -/
theorem sourceSetVolume_possibleImage_lt_top_of_compactBound (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    (h : SourceCompactBound (I := I) v R n) :
    I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) < ⊤ := by
  rcases h with ⟨C, hC⟩
  rw [sourceSetVolume_possibleImage_eq (I := I) v R n hdeg]
  exact lt_of_le_of_lt (b := ENNReal.ofReal C)
    (iSup_le fun j => ENNReal.ofReal_le_ofReal (hC j)) ENNReal.ofReal_lt_top
/-- The hull itself is bounded in log-degree exactly when the paper's compactness input
holds for it.  The value-realized hull constructed from `OriginalInput` alone is *not*
bounded: the scalings of `sourceScalingUnits` are the global points with all components
nonzero, and scaling a fixed image point by the constant point of arbitrarily large
log-degree produces points of the hull of arbitrarily large log-degree.  Hence the
finiteness statement of Corollary 3.12 needs the ring-of-integers (`O`-module)
structure of `IQ(S±_{j+1}; n,◦D⊢_{vQ})`, which bounds the concrete hull; see the audit
note at the end of this file.  What is proved here is the conditional statement with
that bound as an explicit hypothesis. -/
theorem sourceHullVolume_lt_top_of_hullBound (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) {C : Real}
    (hC : ∀ x : I.ThetaPilotPoint v,
      x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) →
        I.sourceLocalLogDegree v x ≤ C) :
    I.sourceHullVolume v R n < ⊤ := by
  unfold sourceHullVolume sourceSetVolume
  exact lt_of_le_of_lt (b := ENNReal.ofReal C)
    (iSup_le fun x => iSup_le fun hx =>
      ENNReal.ofReal_le_ofReal (hC x hx)) ENNReal.ofReal_lt_top

/-! ## 6. The scaled-unit-region reduction

The paper's finiteness proof of Corollary 3.12 uses, beyond the hull operation itself,
the compactness of the `1,◦U_{j,vQ}` and the definition of the log-volume to place the
hull inside a `λ·O` region whose `O`-part is log-shell bounded.  The reduction below
formalizes that shape of argument at the value level: a containment of the hull in a
`λ`-multiple of a unit region of bounded log-degree yields finiteness of the hull
volume.  The containment itself is the named missing input; it is not claimed to
follow from `OriginalInput`. -/

/-- **Scaled-unit-region reduction.**  If the source hull is contained in the
`λ`-multiple of a unit region `O` all of whose points have log-degree at most `C`, then
the log-volume of the hull is finite.  This gives the paper-shaped boundary `hull ⊆ λ·O`
with `O` log-shell bounded, in place of the direct whole-hull bound of
`sourceHullVolume_lt_top_of_hullBound`. -/
theorem sourceHullVolume_lt_top_of_scaledRegionImage (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    {lam : I.ThetaPilotPoint v} {O : Set (I.ThetaPilotPoint v)} {C : Real}
    (hHull : (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ⊆
      scaledRegionImage lam O)
    (hO : ∀ y ∈ O, I.sourceLocalLogDegree v y ≤ C) :
    I.sourceHullVolume v R n < ⊤ := by
  refine I.sourceHullVolume_lt_top_of_hullBound v R n
    (C := I.sourceLocalLogDegree v lam + C) fun x hx => ?_
  obtain ⟨y, hyO, rfl⟩ := hHull hx
  rw [I.sourceLocalLogDegree_mul]
  have hy := hO y hyO
  linarith

/-- The normalized lower bound holds on the hull itself whenever it holds on the
image union, by `P ⊆ φ(P)`. -/
theorem sourceHullVolume_ge_normalized (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    (j₀ : SignedLabel l.value) :
    ENNReal.ofReal ((Fintype.card (SourceVolumeIndex l) : Real) *
        Real.log (I.thetaValueAt (n.val : Int) 0 j₀)) ≤
      I.sourceHullVolume v R n :=
  le_trans
    (sourceSetVolume_possibleImage_ge_normalized (I := I) v R n hdeg j₀)
    (sourceHullVolume_ge_imageVolume (I := I) v R n)

/-! ## 7. The failure of an internal hull bound

The prior audit note recorded informally that the value-realized hull is unbounded
under the all-components-nonzero scalings.  The results below prove this as theorems.

* A constant global point whose every component is the realization of a nonzero
  exponent lies in `sourceScalingUnits` (given the pointwise degree faithfulness under
  which the log-volume formulas hold).
* Consequently the hull log-degree is unbounded above, the hypothesis of
  `sourceHullVolume_lt_top_of_hullBound` is unsatisfiable, and the value-realized hull
  volume is `⊤`.

Hence no strengthening of degree faithfulness can discharge the finiteness: the bound
requires genuinely additional ambient structure, which is exactly what the interface of
`SourceHullCompactnessReduction.lean` names. -/

/-- A constant global point with all components the realization of a nonzero exponent
lies in the source scalings. -/
theorem constantThetaPilotPoint_mem_sourceScalingUnits (v : V)
    (R : I.SourceImageRealization v) {a : Real} (ha : a ≠ 0)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    I.constantThetaPilotPoint v R (Multiplicative.ofAdd a) ∈
      I.sourceScalingUnits v := by
  intro p hp
  have hmem := hdeg a
  rw [I.constantThetaPilotPoint_apply] at hp
  rw [hp, I.logDegreeAt_one] at hmem
  exact ha hmem.symm

/-- Under pointwise degree faithfulness the hull log-degree is unbounded above: scaling
an image point by the constant point of arbitrarily large exponent keeps every component
nonzero and adds the scaling log-degree. -/
theorem sourceHolomorphicHull_logDegree_unbounded (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ∀ C : Real, ∃ x : I.ThetaPilotPoint v,
      x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ∧
        C < I.sourceLocalLogDegree v x := by
  intro C
  obtain ⟨k, hk⟩ := exists_nat_gt (C - I.sourceLocalLogDegree v
    (I.sourceThetaPilotPoint v R n zeroSignedLabel))
  have hs : I.constantThetaPilotPoint v R
      (Multiplicative.ofAdd ((k : Real) + 1)) ∈ I.sourceScalingUnits v :=
    I.constantThetaPilotPoint_mem_sourceScalingUnits v R
      (a := (k : Real) + 1) (ne_of_gt (by positivity)) hdeg
  have hx : I.sourceThetaPilotPoint v R n zeroSignedLabel ∈
      I.sourceHolomorphicHull v R n :=
    I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n zeroSignedLabel
  refine ⟨I.constantThetaPilotPoint v R (Multiplicative.ofAdd ((k : Real) + 1)) *
      I.sourceThetaPilotPoint v R n zeroSignedLabel, ?_, ?_⟩
  · exact I.sourceHolomorphicHull_scaling_mem v R n hs hx
  · rw [I.sourceLocalLogDegree_mul,
      I.sourceLocalLogDegree_constant v R ((k : Real) + 1) hdeg]
    have hcard1 : (1 : Real) ≤ (Fintype.card (SourceVolumeIndex l) : Real) := by
      exact_mod_cast Nat.succ_le_of_lt (sourceVolumeIndex_card_pos l)
    have hprod : (k : Real) + 1 ≤
        (Fintype.card (SourceVolumeIndex l) : Real) * ((k : Real) + 1) := by
      calc (k : Real) + 1 = 1 * ((k : Real) + 1) := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hcard1 (by positivity)
    have hk1 : (k : Real) <
        (Fintype.card (SourceVolumeIndex l) : Real) * ((k : Real) + 1) :=
      lt_of_lt_of_le (lt_add_one (k : Real)) hprod
    linarith

/-- The whole-hull log-degree bound hypothesis of `sourceHullVolume_lt_top_of_hullBound`
is unsatisfiable under pointwise degree faithfulness. -/
theorem not_exists_sourceHullLogDegreeBound_of_degreeFaithful (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ ∃ C : Real, ∀ x : I.ThetaPilotPoint v,
      x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) →
        I.sourceLocalLogDegree v x ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨x, hx, hgt⟩ := I.sourceHolomorphicHull_logDegree_unbounded v R n hdeg C
  exact not_lt_of_ge (hC x hx) hgt

/-- Under pointwise degree faithfulness the value-realized hull log-volume is `⊤`: the
internal finiteness of Corollary 3.12 fails at this level of realization, so the paper
must use the ambient `O`-module structure, not only the hull operation. -/
theorem sourceHullVolume_eq_top_of_degreeFaithful (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    I.sourceHullVolume v R n = ⊤ := by
  have htop : (⊤ : ENNReal) = ⨆ C : Real, ENNReal.ofReal C := by
    rw [eq_comm]
    refine iSup_eq_top.mpr fun a ha => ⟨a.toReal + 1, ?_⟩
    have h0 : (0 : Real) ≤ a.toReal := ENNReal.toReal_nonneg
    calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal ha.ne).symm
      _ < ENNReal.ofReal (a.toReal + 1) :=
          (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  rw [← top_le_iff, htop]
  refine iSup_le fun C => ?_
  obtain ⟨x, hx, hgt⟩ := I.sourceHolomorphicHull_logDegree_unbounded v R n hdeg C
  calc ENNReal.ofReal C ≤ ENNReal.ofReal (I.sourceLocalLogDegree v x) :=
        ENNReal.ofReal_le_ofReal hgt.le
    _ = I.sourcePointVolume v x := rfl
    _ ≤ I.sourceHullVolume v R n := by
        unfold sourceHullVolume sourceSetVolume
        exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)

end OriginalInput
end Theorem311Source

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the source holomorphic hull volume candidate of IUT III
Corollary 3.12. -/
def sourceImageHullVolume : Obligation :=
  { id := "IUT-III.corollary-3.12-source-image-hull-volume"
    source :=
      "IUT III, Remark 3.1.1, (ii)-(iv); Remark 3.9.5, (i), (ii); Corollary 3.12"
    status := VerificationStatus.interface
    note :=
      "The value-monoid realization of the union of possible theta-pilot images and " ++
        "of its holomorphic hull is defined from the actual OriginalInput theta " ++
        "special values, with the paper's least-hull universal property (P1)-(P3) " ++
        "proved. The value-realized theta-image log-volume is proved to be the index " ++
        "cardinality times log of the actual special value, the hull volume dominates " ++
        "the image volume, and conditional finiteness under the named compactness " ++
        "bound is proved. NOT proved: the paper's literal IQ-level hull and its " ++
        "Haar-log-volume, the compactness of the 1,circ U_{j,vQ}, and unconditional " ++
        "finiteness; the abstract hull is in fact unbounded under the all-nonzero " ++
        "scalings, so the ring-of-integers (O-module) structure of " ++
        "IQ(S±_{j+1}; n,circ D^vdash_{vQ}) is required."
    dependsOn :=
      [ "IUT-III.theorem-3.11-original-input-boundary",
        "IUT-I-II.prime-strip-degree-kernel" ] }

end LeanFormal.IUT.Audit
