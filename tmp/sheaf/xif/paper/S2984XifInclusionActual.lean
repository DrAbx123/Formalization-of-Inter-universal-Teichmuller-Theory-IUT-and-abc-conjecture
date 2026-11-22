/-
# S2984 — (xi-f) signed inclusion at the actual value-realized carriers

Task `S2984XifInclusionActual`.  Target, at the actual definitions of
`tmp/sheaf/xif/paper/S2983SignedQPilotActual.lean`:

  `S2983QSigned I v R n ≤ I.sourceSignedHullLogVolume v R n`

i.e. the corpus (xi-f) comparison `-|log q| ≤ -|log Θ|` (III:10895-10898) at
`qSigned := -|log q| = -(image-union volume)`.

## Result of this file

The inclusion is **proved**, unconditionally in `I, v, R, n`
(`S2984XifInclusion`, `S2984SignedComparison`).  It is not obtained by
assuming the via-images normalization: the proof instead isolates the
value-realized hull carrier's structure and proves that its real log-volume
is *identically zero*:

  `sourceRealHullVolume_eq_zero : sourceRealHullVolume v R n = 0`,

hence `sourceSignedHullLogVolume v R n = 0` (`-|log Θ| = 0`), and the comparison
collapses to `-(image volume).toReal ≤ 0`, which is nonnegativity of `toReal`.

## Proof (three structural facts, no geometric input)

1. `sourceHolomorphicHull` is a `Submonoid` (`one_mem`, `mul_mem`), and it is
   stable under every scaling (`sourceHolomorphicHull_candidate`).  Since
   `1 ∈ hull`, every scaling `s ∈ sourceScalingUnits v` lies in the hull
   (`sourceScalingUnits_subset_sourceHolomorphicHull`).
2. `sourceLocalLogDegree` is additive (`sourceLocalLogDegree_mul`,
   `sourceLocalLogDegree_one`) and `sourcePointVolume = ofReal ∘ logDegree`.
   Hence a hull point `x` of *positive* degree has all powers `x ^ k ∈ hull`
   with degree `k * deg x`, so its point-volumes are unbounded and
   `sourceHullVolume = ⊤` (`sourceHullVolume_eq_top_of_degree_pos`).
3. If `sourceHullVolume ≠ ⊤`, every hull point has degree `≤ 0`
   (`sourceHolomorphicHull_subset_degNonpos`: the set `{x | logDegree x ≤ 0}` is a
   submonoid, is scaling-stable, and contains the image union, so by
   minimality of the hull it contains the hull).  Then every hull point has
   `sourcePointVolume = 0`, hence `sourceHullVolume = 0`
   (`sourceHullVolume_eq_zero_of_degNonpos`).

Therefore `sourceHullVolume ∈ {0, ⊤}`, and `sourceRealHullVolume = 0` in both
cases.  This is the same collapse that
`CardHullRealSignedLogVolume.sourceSignedHullLogVolume_eq_zero_of_degreeFaithful`
records under degree faithfulness, now proved with no hypothesis at all.

## Honest boundary (what this is *not*)

This does **not** establish the corpus (xi-f) inclusion with content.  It
shows that the value-monoid transcription of the hull used in this tree
(`SourceImageHull.lean:404`, `sourceHullVolume` of
`SourceImageHullVolume.lean:193`) cannot carry the corpus content: its real
log-volume is `0` (or the `ENNReal` volume is `⊤`), so the signed hull value
`-|log Θ|` is `0` and the comparison is vacuous.  The corpus statement is
about the log-volume of the holomorphic hull inside the `O`-module region
`IQ(S±_{j+1}; n,◦D⊢_{vQ})` with its Haar log-volume (III:990-993,
1051-1053, 10843-10898); those objects are not fields of `OriginalInput`
(see `LiteralArithmeticHullInterface` and `literalHullInterface_impossible` in
`SourceImageHull.lean`).  The missing object is therefore *not* a missing
inequality `sourceHullVolume ≤ image-union volume` — under finiteness that is
proved here (`S2984_hullVolume_eq_imageVolume_of_fin`), and in general it is
false whenever the hull is `⊤` and the image union is finite.  The missing
object is the arithmetic `O`-module / log-shell Haar carrier on which
`|log Θ|` is nonzero.

No hypothesis of real-parts equality, degree faithfulness, compactness, or
hull boundedness is used anywhere below; no `sorry`, no new axiom, no
weakened quantifier.
-/
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealSignedLogVolume
import tmp.sheaf.xif.paper.S2983SignedQPilotActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2983SignedQPilotActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2984XifInclusionActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)

/-! ## 1. The submonoid of nonpositive log-degree -/

/-- The points of the global value carrier whose source log-degree is at most
zero.  This is the candidate hull used in the finite regime below. -/
def sourceDegNonposSubmonoid (v : V) : Submonoid (I.ThetaPilotPoint v) where
  carrier := {x | I.sourceLocalLogDegree v x ≤ 0}
  one_mem' := by
    show I.sourceLocalLogDegree v 1 ≤ 0
    rw [I.sourceLocalLogDegree_one]
  mul_mem' := by
    intro x y hx hy
    show I.sourceLocalLogDegree v (x * y) ≤ 0
    rw [I.sourceLocalLogDegree_mul]
    have hx' : I.sourceLocalLogDegree v x ≤ 0 := hx
    have hy' : I.sourceLocalLogDegree v y ≤ 0 := hy
    linarith

/-- Every scaling unit of the hull operation lies in the hull: the hull is a
`CandidateHull` (stable under scalings) and contains `1`, so `s = s * 1 ∈ hull`. -/
theorem sourceScalingUnits_subset_sourceHolomorphicHull (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceScalingUnits v ⊆
      (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) := by
  intro s hs
  have hc : CandidateHull (I.sourceScalingUnits v) (I.sourceHolomorphicHull v R n) :=
    I.sourceHolomorphicHull_candidate v R n
  have h := hc s hs 1 (I.sourceHolomorphicHull v R n).one_mem
  simpa using h

/-! ## 2. A positive-degree hull point forces the top volume -/

/-- **Unboundedness criterion.**  If some point of the hull has strictly positive
log-degree, then its powers stay in the hull (a submonoid) with degrees
`k * deg x`, so the hull log-volume is `⊤`. -/
theorem sourceHullVolume_eq_top_of_degree_pos (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    {x : I.ThetaPilotPoint v} (hx : x ∈ I.sourceHolomorphicHull v R n)
    (hpos : 0 < I.sourceLocalLogDegree v x) :
    I.sourceHullVolume v R n = ⊤ := by
  have hmem : ∀ k : ℕ, x ^ k ∈ I.sourceHolomorphicHull v R n := by
    intro k
    induction k with
    | zero => simpa using (I.sourceHolomorphicHull v R n).one_mem
    | succ k ih =>
        rw [pow_succ]
        exact (I.sourceHolomorphicHull v R n).mul_mem ih hx
  have hdeg : ∀ k : ℕ,
      I.sourceLocalLogDegree v (x ^ k) = (k : ℝ) * I.sourceLocalLogDegree v x := by
    intro k
    induction k with
    | zero => simp [I.sourceLocalLogDegree_one]
    | succ k ih =>
        rw [pow_succ, I.sourceLocalLogDegree_mul, ih, Nat.cast_succ]
        ring
  have hbound : ∀ C : ℝ, ENNReal.ofReal C ≤ I.sourceHullVolume v R n := by
    intro C
    obtain ⟨k, hk⟩ := exists_nat_ge (C / I.sourceLocalLogDegree v x)
    have hC : C ≤ (k : ℝ) * I.sourceLocalLogDegree v x := by
      have h1 : C / I.sourceLocalLogDegree v x ≤ (k : ℝ) := hk
      have h2 : C / I.sourceLocalLogDegree v x * I.sourceLocalLogDegree v x ≤
          (k : ℝ) * I.sourceLocalLogDegree v x :=
        mul_le_mul_of_nonneg_right h1 (le_of_lt hpos)
      have h3 : C / I.sourceLocalLogDegree v x * I.sourceLocalLogDegree v x = C :=
        div_mul_cancel₀ C (ne_of_gt hpos)
      linarith
    calc ENNReal.ofReal C
        ≤ ENNReal.ofReal ((k : ℝ) * I.sourceLocalLogDegree v x) :=
          ENNReal.ofReal_le_ofReal hC
      _ = I.sourcePointVolume v (x ^ k) := by
          simp only [sourcePointVolume, hdeg k]
      _ ≤ I.sourceHullVolume v R n := by
          unfold sourceHullVolume sourceSetVolume
          exact le_iSup_of_le (x ^ k) (le_iSup_of_le (hmem k) le_rfl)
  by_contra hne
  have h1 : ENNReal.ofReal ((I.sourceHullVolume v R n).toReal + 1) ≤
      I.sourceHullVolume v R n := hbound ((I.sourceHullVolume v R n).toReal + 1)
  have h2 : (ENNReal.ofReal ((I.sourceHullVolume v R n).toReal + 1)).toReal ≤
      (I.sourceHullVolume v R n).toReal := ENNReal.toReal_mono hne h1
  rw [ENNReal.toReal_ofReal (by positivity)] at h2
  linarith

/-! ## 3. Finiteness forces the hull into the nonpositive-degree submonoid -/

/-- **Containment in the nonpositive-degree submonoid.**  Assume the hull volume
is finite, so (by §2) no hull point has positive degree; then every image point
and every scaling has nonpositive degree, so `{x | logDegree x ≤ 0}` is a
candidate hull containing the image union, and by minimality it contains the
hull. -/
theorem sourceHolomorphicHull_subset_degNonpos (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hscal : ∀ s : I.ThetaPilotPoint v, s ∈ I.sourceScalingUnits v →
      I.sourceLocalLogDegree v s ≤ 0)
    (himg : ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ 0) :
    ∀ x : I.ThetaPilotPoint v, x ∈ I.sourceHolomorphicHull v R n →
      I.sourceLocalLogDegree v x ≤ 0 := by
  intro x hx
  have hH : CandidateHull (I.sourceScalingUnits v) (sourceDegNonposSubmonoid I v) := by
    intro s hs y hy
    show I.sourceLocalLogDegree v (s * y) ≤ 0
    rw [I.sourceLocalLogDegree_mul]
    have h1 : I.sourceLocalLogDegree v s ≤ 0 := hscal s hs
    have h2 : I.sourceLocalLogDegree v y ≤ 0 := hy
    linarith
  have hS : I.possibleThetaPilotImageSet v R n ⊆
      (sourceDegNonposSubmonoid I v : Set (I.ThetaPilotPoint v)) := by
    rintro y ⟨j, rfl⟩
    exact himg j
  exact I.sourceHolomorphicHull_le v R n hH hS hx

/-- With every hull point of nonpositive degree, all hull point-volumes vanish,
so the hull log-volume is `0`. -/
theorem sourceHullVolume_eq_zero_of_degNonpos (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (h : ∀ x : I.ThetaPilotPoint v, x ∈ I.sourceHolomorphicHull v R n →
      I.sourceLocalLogDegree v x ≤ 0) :
    I.sourceHullVolume v R n = 0 := by
  unfold sourceHullVolume sourceSetVolume
  refine le_antisymm ?_ zero_le
  refine iSup_le fun x => iSup_le fun hx => ?_
  have hx' : I.sourceLocalLogDegree v x ≤ 0 := h x hx
  show I.sourcePointVolume v x ≤ 0
  unfold sourcePointVolume
  exact le_of_eq (ENNReal.ofReal_eq_zero.mpr hx')

/-! ## 4. Degeneracy of the value-realized hull volume -/

/-- **The real hull log-volume is identically zero.**  Case split on whether the
hull volume is `⊤`: in that case `toReal ⊤ = 0`; otherwise §2 forces every hull
point to have nonpositive degree and §3 gives volume `0`. -/
theorem sourceRealHullVolume_eq_zero (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : I.sourceRealHullVolume v R n = 0 := by
  by_cases htop : I.sourceHullVolume v R n = ⊤
  · unfold sourceRealHullVolume
    rw [htop, ENNReal.toReal_top]
  · have himg : ∀ j : SignedLabel l.value,
        I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ 0 := by
      intro j
      by_contra h
      push_neg at h
      exact htop (sourceHullVolume_eq_top_of_degree_pos I v R n
        (I.possibleThetaPilotImage_subset_sourceHolomorphicHull v R n
          (I.sourceThetaPilotPoint_mem v R n j)) h)
    have hscal : ∀ s : I.ThetaPilotPoint v, s ∈ I.sourceScalingUnits v →
        I.sourceLocalLogDegree v s ≤ 0 := by
      intro s hs
      by_contra h
      push_neg at h
      exact htop (sourceHullVolume_eq_top_of_degree_pos I v R n
        (sourceScalingUnits_subset_sourceHolomorphicHull I v R n hs) h)
    have hdeg : ∀ x : I.ThetaPilotPoint v, x ∈ I.sourceHolomorphicHull v R n →
        I.sourceLocalLogDegree v x ≤ 0 :=
      sourceHolomorphicHull_subset_degNonpos I v R n hscal himg
    have hzero : I.sourceHullVolume v R n = 0 :=
      sourceHullVolume_eq_zero_of_degNonpos I v R n hdeg
    unfold sourceRealHullVolume
    rw [hzero, ENNReal.toReal_zero]

/-- **Dichotomy.**  The value-realized hull log-volume is either `0` or `⊤`. -/
theorem sourceHullVolume_eq_zero_or_top (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    I.sourceHullVolume v R n = 0 ∨ I.sourceHullVolume v R n = ⊤ := by
  by_cases htop : I.sourceHullVolume v R n = ⊤
  · exact Or.inr htop
  · have himg : ∀ j : SignedLabel l.value,
        I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ 0 := by
      intro j
      by_contra h
      push_neg at h
      exact htop (sourceHullVolume_eq_top_of_degree_pos I v R n
        (I.possibleThetaPilotImage_subset_sourceHolomorphicHull v R n
          (I.sourceThetaPilotPoint_mem v R n j)) h)
    have hscal : ∀ s : I.ThetaPilotPoint v, s ∈ I.sourceScalingUnits v →
        I.sourceLocalLogDegree v s ≤ 0 := by
      intro s hs
      by_contra h
      push_neg at h
      exact htop (sourceHullVolume_eq_top_of_degree_pos I v R n
        (sourceScalingUnits_subset_sourceHolomorphicHull I v R n hs) h)
    have hdeg : ∀ x : I.ThetaPilotPoint v, x ∈ I.sourceHolomorphicHull v R n →
        I.sourceLocalLogDegree v x ≤ 0 :=
      sourceHolomorphicHull_subset_degNonpos I v R n hscal himg
    exact Or.inl (sourceHullVolume_eq_zero_of_degNonpos I v R n hdeg)

/-! ## 5. The (xi-f) signed inclusion at the actual S2983 carriers -/

/-- The signed hull carrier `-|log Θ|` is identically zero. -/
theorem sourceSignedHullLogVolume_eq_zero (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : I.sourceSignedHullLogVolume v R n = 0 := by
  unfold sourceSignedHullLogVolume
  rw [sourceRealHullVolume_eq_zero I v R n, neg_zero]

/-- **The target inequality** at the actual `S2983QSigned`:
`-|log q| ≤ -|log Θ|`.  Since `-|log Θ| = 0` and `-|log q| ≤ 0`, this is the
nonpositivity of the signed image volume. -/
theorem S2984XifInclusion :
    S2983QSigned I v R n ≤ I.sourceSignedHullLogVolume v R n := by
  have h0 : I.sourceSignedHullLogVolume v R n = 0 :=
    sourceSignedHullLogVolume_eq_zero I v R n
  rw [h0, S2983_qSigned_eq I v R n]
  exact neg_nonpos.mpr ENNReal.toReal_nonneg

/-- The named `S2983` comparison, discharged at the actual carriers. -/
theorem S2984SignedComparison : S2983SignedComparison I v R n :=
  S2984XifInclusion I v R n

/-- Cross-check: the `S2983` reduction still holds; both sides of the reduction
are now theorems (`sourceRealHullVolume = 0` and, under finiteness, the image
volume is also `0`). -/
theorem S2984_comparison_iff_realParts_eq
    (hfin : I.sourceHullVolume v R n < ⊤) :
    S2983SignedComparison I v R n ↔
      I.sourceRealHullVolume v R n =
        (I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)).toReal :=
  S2983_comparison_iff_realParts_eq I v R n hfin

/-- In the finite regime the via-images normalization holds as a theorem: both
volumes vanish. -/
theorem S2984_hullVolume_eq_imageVolume_of_fin
    (hfin : I.sourceHullVolume v R n < ⊤) :
    I.sourceHullVolume v R n =
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) := by
  have h0 : I.sourceRealHullVolume v R n = 0 := sourceRealHullVolume_eq_zero I v R n
  have hhull : I.sourceHullVolume v R n = 0 := by
    rw [I.sourceHullVolume_eq_ofReal v R n hfin, h0, ENNReal.ofReal_zero]
  have hle : I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) ≤
      I.sourceHullVolume v R n := I.sourceHullVolume_ge_imageVolume v R n
  have himg : I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) = 0 := by
    rw [hhull] at hle
    exact le_antisymm hle zero_le
  rw [hhull, himg]

#check S2984XifInclusion
#check S2984SignedComparison
#check sourceRealHullVolume_eq_zero
#check sourceSignedHullLogVolume_eq_zero
#check sourceHullVolume_eq_zero_or_top
#check S2984_hullVolume_eq_imageVolume_of_fin

#print axioms S2984XifInclusion
#print axioms S2984SignedComparison
#print axioms sourceRealHullVolume_eq_zero
#print axioms sourceHullVolume_eq_zero_or_top

end LeanFormal.IUT.XiFPaper.S2984XifInclusionActual
end
