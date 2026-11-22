import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiring
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealEdgeNormalizationReduction

/-!
# Card-HULLREAL R9-(c)/(d): multiplicative action and max-stability dichotomy

Task `hunit-epsilon-transfer-20261016`, R9-(c)/(d) attack round (report section
19).  The previous round (section 18 / `CardHullRealEdgeNormalizationReduction`)
reduced R9 to a product-edge normalization `hprod` and named the interface-level
edge bound.  This file attacks the two named remaining pieces:

* (c) Multiplicative action and `dot-mu` decomposition.  The interface
  structure `LogVolumeScaleDecomposition` freezes the log-coordinate form of
  [AbsTopIII] Proposition 5.7, (i), (b): a right multiplicative action
  `A |-> (A . x)` on sets, an additive log-volume decomposition
  `mu^log(A . x) = mu^log(A) + dot-mu^log(x)`, normalization `mu^log(O) = 0`,
  and `dot-mu^log(x) = mu^log(x . O)`.  The derived laws: `dot-mu^log(1) = 0`,
  additivity of `dot-mu^log` under multiplication, invariance when the factor
  vanishes, and nonpositivity propagation along finite products and powers (the
  abstract form of "every hull point is a contraction").  Value-layer binding
  lemmas transfer log-degree bounds along the concrete right multiplication
  action `sourceMulImage` on `ThetaPilotPoint`s.  The real-line test carrier of
  the carrier-line report section 14 (normalized Haar volume, additive
  translation half) matches the additive-translation fragment; the
  multiplicative decomposition frozen here is the piece its gap list, item 1,
  records as not formalized.

* (d) Max-stability dichotomy.  On the hull, the product-edge normalization
  `vol(x * y) <= max (vol x) (vol y)` holds exactly when every hull point has
  nonpositive log-degree (the contractive regime, where all point volumes
  vanish); any hull point of positive log-degree refutes it, with its square as
  an explicit witness.  This negative direction is unconditional, does not
  involve the pointwise degree-faithfulness premise of the section 18
  calibration (whose premise space is empty by the O1 observation), and hence
  is not a collapsed-regime statement: it says that max-stability without
  contraction is impossible at the value layer.

* Sharpening of R9.  Combining the dichotomy with the finiteness of the edge
  volume gives an exact value-layer characterization:
  `hull <= image` iff every hull point has nonpositive log-degree, iff every
  theta-pilot image and scaling unit does.  The section 18 card is thus refined:
  the sharp value-layer content of R9 is the sign control of the generators
  (whose corpus source is the negativity of `-|log(Theta)|`, III:10390, plus
  the log-shell/tensor-packet identification, III:10851-10863); the R9 body
  itself remains unproved.

* Consumer transfer for the theta slot: `CertificateHullWiring` lines 155/204
  consume `hTheta : W.logVolume W.hull <= ofReal theta`.  The two theorems
  `iqHullEdgeBound_certificate_of_imageSetThetaBound` and
  `iqHullEdgeBound_cor312Conclusion_of_imageSetThetaBound` re-supply that slot
  from an image-set-level bound (section 18 transfer), for the root to relay to
  the CertificateHullWiring line; the consumers are imported read-only and are
  not modified here.

Boundaries: R9 body unproved (remains the card of section 18, refined here);
no claim that a positive-log-degree hull point exists in any concrete instance
of the tree (the dichotomy is a conditional statement); the multiplicative
structure is an interface structure, not instantiated on the paper carrier.
-/

namespace LeanFormal.IUT

noncomputable section

universe u v ua uv upi umon ui

/-! ## 1. (c) The multiplicative action / `dot-mu` decomposition interface -/

/-- The log-coordinate form of the log-volume decomposition law of
[AbsTopIII] Proposition 5.7, (i), (b): a right multiplicative action on sets
(`A |-> A . x`), an additive log-volume split with factor `logScale`,
normalization `logVolume unitRegion = 0`, and `logScale x = logVolume(unitRegion . x)`.
The carrier-line report section 14 formalizes the additive-translation/constant-
scaling fragment of the normalized Haar volume; the multiplicative decomposition
frozen here is the remaining named piece of its gap list, item 1. -/
structure LogVolumeScaleDecomposition (X : Type u) [Monoid X] where
  /-- The log-volume functional on regions, in log coordinates (`mu^log`). -/
  logVolume : Set X → ℝ
  /-- The distinguished unit region `O` of the normalization. -/
  unitRegion : Set X
  /-- Normalization: `mu(O) = 1` in multiplicative coordinates, i.e.
  `mu^log(O) = 0`. -/
  normalization : logVolume unitRegion = 0
  /-- The additive `dot-mu^log` factor of the action. -/
  logScale : X → ℝ
  /-- The decomposition law `mu^log(A . x) = mu^log(A) + dot-mu^log(x)`. -/
  decomposition : ∀ (x : X) (A : Set X),
    logVolume ((fun a => a * x) '' A) = logVolume A + logScale x

namespace LogVolumeScaleDecomposition

variable {X : Type u} [Monoid X] (D : LogVolumeScaleDecomposition X)

/-- `dot-mu^log(x) = mu^log(x . O)`: the factor is the log-volume of the
`x`-translate of the unit region (Proposition 5.7, (i), (b), first clause). -/
theorem logScale_eq_logVolume_shift_unitRegion (x : X) :
    D.logVolume ((fun a => a * x) '' D.unitRegion) = D.logScale x := by
  have h := D.decomposition x D.unitRegion
  rw [D.normalization] at h
  exact h.trans (zero_add (D.logScale x))

/-- `dot-mu^log(1) = 0`. -/
theorem logScale_one : D.logScale 1 = 0 := by
  have hO : (fun a => a * 1) '' D.unitRegion = D.unitRegion := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
    · intro hb
      exact ⟨b, hb, mul_one b⟩
  have h := D.decomposition 1 D.unitRegion
  rw [hO] at h
  linarith

/-- Additivity of `dot-mu^log` under the monoid multiplication: the factor is
an additive homomorphism into `(Real, +)` (Proposition 5.7, (i), (b), second
clause, in log coordinates). -/
theorem logScale_mul (x y : X) :
    D.logScale (x * y) = D.logScale x + D.logScale y := by
  have hcomp : (fun a => a * (x * y)) '' D.unitRegion =
      (fun b => b * y) '' ((fun a => a * x) '' D.unitRegion) := by
    rw [Set.image_image]
    simp only [mul_assoc]
  have h1 := D.decomposition (x * y) D.unitRegion
  rw [hcomp, D.decomposition y ((fun a => a * x) '' D.unitRegion),
    D.decomposition x D.unitRegion] at h1
  linarith

/-- Invariance of the log-volume under the action when the factor vanishes:
the factor-vanishing form of the unit-group invariance of Proposition 5.7, (i),
(b), third clause. -/
theorem logVolume_shift_eq_of_logScale_eq_zero {x : X} (hx : D.logScale x = 0)
    (A : Set X) :
    D.logVolume ((fun a => a * x) '' A) = D.logVolume A :=
  (D.decomposition x A).trans (by rw [hx, add_zero])

/-- Nonpositivity of the factor propagates along finite products: the abstract
form of "every point generated by contractions is a contraction". -/
theorem logScale_listProd_le_zero {G : Set X}
    (hG : ∀ g ∈ G, D.logScale g ≤ 0) (L : List X) :
    (∀ g ∈ L, g ∈ G) → D.logScale L.prod ≤ 0 := by
  induction L with
  | nil => intro _; simp [D.logScale_one]
  | cons x L ih =>
      intro hL
      rw [List.prod_cons, D.logScale_mul]
      have hx := hG x (hL x List.mem_cons_self)
      have hL' := ih (fun g hg => hL g (List.mem_cons_of_mem x hg))
      linarith

/-- Nonpositivity of the factor propagates along powers. -/
theorem logScale_pow_le_zero {G : Set X} (hG : ∀ g ∈ G, D.logScale g ≤ 0)
    {g : X} (hg : g ∈ G) (k : ℕ) : D.logScale (g ^ k) ≤ 0 := by
  induction k with
  | zero => simpa using (D.logScale_one).le
  | succ k ih =>
      rw [pow_succ, D.logScale_mul]
      linarith [hG g hg, ih]

end LogVolumeScaleDecomposition

/-- A consistency witness: the all-zero data on `Multiplicative Nat` satisfies
the decomposition interface.  This is a check on the structure only, not a
model of the paper's carrier. -/
def multiplicativeNatScaleWitness :
    LogVolumeScaleDecomposition (Multiplicative ℕ) where
  logVolume := fun _ => 0
  unitRegion := Set.univ
  normalization := rfl
  logScale := fun _ => 0
  decomposition := fun _ _ => by simp

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 2. (c) value-layer binding: the right multiplication action -/

/-- The right multiplication action of a global value point on sets of global
value points: the concrete carrier of the `x . A` action of the decomposition
law `sourceLocalLogDegree_mul`. -/
def sourceMulImage (v : V) (x : I.ThetaPilotPoint v)
    (A : Set (I.ThetaPilotPoint v)) : Set (I.ThetaPilotPoint v) :=
  (fun a => a * x) '' A

/-- **Bound transfer along the action.**  If every point of `A` has
log-degree at most `C`, then every point of the `x`-translate has log-degree at
most `C + mu_log(x)`: the value-layer form of the decomposition
`mu^log(A . x) = mu^log(A) + dot-mu^log(x)` as a bound-transfer rule. -/
theorem sourceLocalLogDegree_mem_sourceMulImage_le (v : V)
    (x : I.ThetaPilotPoint v) {A : Set (I.ThetaPilotPoint v)} {C : ℝ}
    (hA : ∀ a ∈ A, I.sourceLocalLogDegree v a ≤ C) :
    ∀ b ∈ I.sourceMulImage v x A,
      I.sourceLocalLogDegree v b ≤ C + I.sourceLocalLogDegree v x := by
  rintro b ⟨a, ha, rfl⟩
  rw [I.sourceLocalLogDegree_mul]
  exact add_le_add (hA a ha) le_rfl

/-- **Set-level decomposition bound.**  The log-volume of the translate of a
region whose log-degrees are capped by `C` is at most
`ofReal (C + mu_log(x))`: the sup-level form of the decomposition law on the
concrete value layer. -/
theorem sourceSetVolume_sourceMulImage_le_of_forall_logDegree_le (v : V)
    (x : I.ThetaPilotPoint v) {A : Set (I.ThetaPilotPoint v)} {C : ℝ}
    (hA : ∀ a ∈ A, I.sourceLocalLogDegree v a ≤ C) :
    I.sourceSetVolume v (I.sourceMulImage v x A) ≤
      ENNReal.ofReal (C + I.sourceLocalLogDegree v x) := by
  unfold sourceSetVolume
  refine iSup_le fun b => ?_
  refine iSup_le fun hb => ?_
  obtain ⟨a, ha, rfl⟩ := hb
  unfold sourcePointVolume
  rw [I.sourceLocalLogDegree_mul]
  exact ENNReal.ofReal_le_ofReal (add_le_add (hA a ha) le_rfl)

/-! ## 3. (d) max-stability dichotomy on the hull -/

/-- Log-degree of powers: `mu_log(x ^ k) = k * mu_log(x)`. -/
theorem sourceLocalLogDegree_pow (v : V) (x : I.ThetaPilotPoint v) (k : ℕ) :
    I.sourceLocalLogDegree v (x ^ k) =
      (k : ℝ) * I.sourceLocalLogDegree v x := by
  induction k with
  | zero => simp [I.sourceLocalLogDegree_one]
  | succ k ih =>
      rw [pow_succ, I.sourceLocalLogDegree_mul, ih]
      push_cast
      ring

/-- **Pointwise failure of max-stability at a positive-degree point.**  A point
of positive log-degree violates `vol(x * x) <= max (vol x) (vol x)`: squaring
doubles the log-degree and the volume of the square strictly exceeds the
factor maximum.  No degree-faithfulness hypothesis is involved. -/
theorem not_sourcePointVolume_mul_le_max_self_of_logDegree_pos (v : V)
    (x : I.ThetaPilotPoint v) (hpos : 0 < I.sourceLocalLogDegree v x) :
    ¬ I.sourcePointVolume v (x * x) ≤
      max (I.sourcePointVolume v x) (I.sourcePointVolume v x) := by
  intro h
  have h2 : I.sourceLocalLogDegree v x + I.sourceLocalLogDegree v x =
      2 * I.sourceLocalLogDegree v x := by ring
  have hprod : I.sourcePointVolume v (x * x) =
      ENNReal.ofReal (2 * I.sourceLocalLogDegree v x) := by
    unfold sourcePointVolume
    rw [I.sourceLocalLogDegree_mul, h2]
  rw [hprod, max_self] at h
  have hle : 2 * I.sourceLocalLogDegree v x ≤ I.sourceLocalLogDegree v x :=
    (ENNReal.ofReal_le_ofReal_iff hpos.le).mp h
  linarith

/-- **Unconditional negative direction (non-collapsed).**  If the hull contains
a point of positive log-degree, the product-edge normalization fails on the
hull, with the square of that point as witness.  This refutes max-stability
without the empty degree-faithfulness premise of the section 18 calibration. -/
theorem not_sourcePointVolume_mul_le_max_on_hull_of_exists_logDegree_pos
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (h : ∃ x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
      0 < I.sourceLocalLogDegree v x) :
    ¬ (∀ x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        ∀ y ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
          I.sourcePointVolume v (x * y) ≤
            max (I.sourcePointVolume v x) (I.sourcePointVolume v y)) := by
  rintro hmax
  obtain ⟨x, hx, hpos⟩ := h
  exact not_sourcePointVolume_mul_le_max_self_of_logDegree_pos I v x hpos
    (hmax x hx x hx)

/-- **Positive direction on a contractive hull.**  If every hull point has
nonpositive log-degree, all hull point volumes vanish and max-stability holds
(the contractive regime; here the normalization is trivially zero). -/
theorem sourcePointVolume_mul_le_max_on_hull_of_logDegree_nonpos
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (h : ∀ z ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
      I.sourceLocalLogDegree v z ≤ 0) :
    ∀ x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
      ∀ y ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        I.sourcePointVolume v (x * y) ≤
          max (I.sourcePointVolume v x) (I.sourcePointVolume v y) := by
  intro x hx y hy
  have hxy : I.sourcePointVolume v (x * y) = 0 := by
    unfold sourcePointVolume
    rw [I.sourceLocalLogDegree_mul]
    exact ENNReal.ofReal_eq_zero.mpr (by linarith [h x hx, h y hy])
  rw [hxy]
  exact zero_le

/-- **Max-stability dichotomy.**  On the hull, the product-edge normalization
holds exactly when every hull point is a contraction.  Hence max-stability is
available only in the collapsed (all-zero) regime and fails as soon as the hull
carries a point of positive log-degree. -/
theorem sourcePointVolume_mul_le_max_on_hull_iff_logDegree_nonpos
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    (∀ x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        ∀ y ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
          I.sourcePointVolume v (x * y) ≤
            max (I.sourcePointVolume v x) (I.sourcePointVolume v y)) ↔
      (∀ z ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        I.sourceLocalLogDegree v z ≤ 0) := by
  refine ⟨fun hmax => ?_,
    fun h => sourcePointVolume_mul_le_max_on_hull_of_logDegree_nonpos I v R n h⟩
  by_contra h'
  obtain ⟨z, hz⟩ := not_forall.mp h'
  rw [Classical.not_imp] at hz
  exact not_sourcePointVolume_mul_le_max_on_hull_of_exists_logDegree_pos I v R n
    ⟨z, hz.1, not_le.mp hz.2⟩ hmax

/-! ## 4. Sharp characterization of R9 at the value layer -/

/-- The hull volume vanishes on a contractive hull. -/
theorem sourceHullVolume_eq_zero_of_hull_logDegree_nonpos (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (h : ∀ z ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
      I.sourceLocalLogDegree v z ≤ 0) :
    I.sourceHullVolume v R n = 0 := by
  unfold sourceHullVolume sourceSetVolume
  exact le_antisymm
    (iSup_le fun z => iSup_le fun hz =>
      le_of_eq (I.sourcePointVolume_eq_zero_of_logDegree_nonpos v z (h z hz)))
    zero_le

/-- **R9 fails at any positive-degree hull point.**  Since the powers of a
positive-degree hull point remain in the hull and their volumes grow linearly,
the hull volume cannot be bounded by the edge volume, which is finite.  This is
the sharp negative direction of the R9 characterization; it uses no
degree-faithfulness premise. -/
theorem not_sourceHullVolume_le_imageVolume_of_hull_logDegree_pos (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (h : ∃ x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
      0 < I.sourceLocalLogDegree v x) :
    ¬ I.sourceHullVolume v R n ≤ I.sourceImageVolume v R n := by
  rintro hvol
  obtain ⟨x, hx, hpos⟩ := h
  have hBlt : I.sourceImageVolume v R n < ⊤ := sourceImageVolume_lt_top I v R n
  have hsup : ∀ k : ℕ,
      ENNReal.ofReal ((k : ℝ) * I.sourceLocalLogDegree v x) ≤
        I.sourceHullVolume v R n := by
    intro k
    have hpow : x ^ k ∈
        (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) :=
      Submonoid.pow_mem (I.sourceHolomorphicHull v R n) hx k
    calc ENNReal.ofReal ((k : ℝ) * I.sourceLocalLogDegree v x)
        = I.sourcePointVolume v (x ^ k) := by
          unfold sourcePointVolume
          rw [I.sourceLocalLogDegree_pow]
      _ ≤ I.sourceHullVolume v R n := by
          unfold sourceHullVolume sourceSetVolume
          exact le_iSup_of_le (x ^ k) (le_iSup_of_le hpow le_rfl)
  have hle_all : ∀ k : ℕ,
      (k : ℝ) * I.sourceLocalLogDegree v x ≤
        (I.sourceImageVolume v R n).toReal := by
    intro k
    have h1 := hsup k
    have h2 : ENNReal.ofReal ((k : ℝ) * I.sourceLocalLogDegree v x) ≤
        I.sourceImageVolume v R n := le_trans h1 hvol
    rw [← ENNReal.ofReal_toReal (ne_top_of_lt hBlt)] at h2
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h2
  obtain ⟨k, hk⟩ := exists_nat_gt
    ((I.sourceImageVolume v R n).toReal / I.sourceLocalLogDegree v x)
  have hk' : (I.sourceImageVolume v R n).toReal <
      (k : ℝ) * I.sourceLocalLogDegree v x := by
    have h' := mul_lt_mul_of_pos_right hk hpos
    rwa [div_mul_cancel₀ _ (ne_of_gt hpos)] at h'
  exact not_lt_of_ge (hle_all k) hk'

/-- **Sharp value-layer characterization of R9.**  The inequality `hull <=
image` holds exactly when every hull point has nonpositive log-degree: the
sharp content of R9 at the value layer is the sign control of the hull points
(corpus source: negativity of `-|log(Theta)|`, III:10390, plus the log-shell /
tensor-packet identification of the possible images, III:10851-10863). -/
theorem sourceHullVolume_le_imageVolume_iff_hull_logDegree_nonpos (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceHullVolume v R n ≤ I.sourceImageVolume v R n ↔
      ∀ z ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        I.sourceLocalLogDegree v z ≤ 0 := by
  constructor
  · intro hvol
    by_contra h'
    obtain ⟨z, hz⟩ := not_forall.mp h'
    rw [Classical.not_imp] at hz
    exact not_sourceHullVolume_le_imageVolume_of_hull_logDegree_pos I v R n
      ⟨z, hz.1, not_le.mp hz.2⟩ hvol
  · intro h
    rw [sourceHullVolume_eq_zero_of_hull_logDegree_nonpos I v R n h]
    exact zero_le

/-- **Generator-level sharp characterization.**  R9 holds exactly when every
theta-pilot image and every scaling unit is a contraction: the generator form of
the characterization, whose forward direction is the new unconditional
negative and whose backward direction is the section 17 reduction (R7). -/
theorem sourceHullVolume_le_imageVolume_iff_generators_nonpos (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceHullVolume v R n ≤ I.sourceImageVolume v R n ↔
      (∀ j : SignedLabel l.value,
        I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ 0) ∧
      (∀ s ∈ I.sourceScalingUnits v, I.sourceLocalLogDegree v s ≤ 0) := by
  refine ⟨fun hvol => ⟨?_, ?_⟩, fun ⟨himg, hscal⟩ => ?_⟩
  · by_contra h'
    obtain ⟨j, hj⟩ := not_forall.mp h'
    exact not_sourceHullVolume_le_imageVolume_of_hull_logDegree_pos I v R n
      ⟨I.sourceThetaPilotPoint v R n j,
        I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n j,
        not_le.mp hj⟩ hvol
  · by_contra h'
    obtain ⟨s, hsnot⟩ := not_forall.mp h'
    obtain ⟨hs, hspos⟩ := Classical.not_imp.mp hsnot
    exact not_sourceHullVolume_le_imageVolume_of_hull_logDegree_pos I v R n
      ⟨s, sourceScalingUnits_subset_sourceHolomorphicHull I v R n hs,
        not_le.mp hspos⟩ hvol
  · simpa only [sourceImageVolume] using
      I.sourceHullVolume_le_imageVolume_of_generator_nonpos v R n himg hscal

end OriginalInput
end Theorem311Source

/-! ## 5. Theta-slot re-supply for the certificate consumers -/

/-- **Consumer transfer: certificate with an image-set-level theta bound.**
The `CertificateHullWiring` certificate constructor `iqHullCertificate` consumes
`hTheta : W.logVolume W.hull <= ofReal theta` (line 155).  Under the section 18
edge-bound interface, the hull-level slot is re-supplied from an image-set-level
bound, with all other arguments unchanged; the consumer file is imported
read-only. -/
def iqHullEdgeBound_certificate_of_imageSetThetaBound {X : Type u}
    (W : IQHullEdgeBoundInterface X)
    {label : Type v} [Fintype label] (pt : label → X)
    (hpt : ∀ i, pt i ∈ W.imageSet) (data : WeightedValues label)
    (hvalue : ∀ i, data.value i =
      (iqHullFiniteHull W.toIQHullLogVolumeInterface pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i) (q θ : ℝ)
    (hq : ENNReal.ofReal q ≤ W.logVolume W.imageSet)
    (himgθ : W.logVolume W.imageSet ≤ ENNReal.ofReal θ)
    (hθ0 : 0 ≤ θ) (hqneg : q < 0) :
    StepXIFiniteCertificate label :=
  iqHullCertificate W.toIQHullLogVolumeInterface pt hpt data hvalue hw q θ hq
    (iqHullEdgeBound_logVolume_hull_le_ofReal W himgθ) hθ0 hqneg

/-- **Consumer transfer: Cor 3.12 conclusion with an image-set-level theta
bound.**  The headline composition `iqHullCor312Conclusion` (line 204) with its
hull-level theta slot re-supplied at the image set; IPL/SHE/APT remain external
inputs, exactly as in the existing bridge. -/
theorem iqHullEdgeBound_cor312Conclusion_of_imageSetThetaBound {X : Type u}
    (W : IQHullEdgeBoundInterface X)
    {label : Type v} [Fintype label] (pt : label → X)
    (hpt : ∀ i, pt i ∈ W.imageSet) (data : WeightedValues label)
    (hvalue : ∀ i, data.value i =
      (iqHullFiniteHull W.toIQHullLogVolumeInterface pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i) (q θ : ℝ)
    (hq : ENNReal.ofReal q ≤ W.logVolume W.imageSet)
    (himgθ : W.logVolume W.imageSet ≤ ENNReal.ofReal θ)
    (hθ0 : 0 ≤ θ) (hqneg : q < 0)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((iqHullEdgeBound_certificate_of_imageSetThetaBound W pt hpt data hvalue
          hw q θ hq himgθ hθ0 hqneg).toContract
        (iqHullLinkEvidence W.toIQHullLogVolumeInterface pt hpt data hvalue hw
          q θ hq (iqHullEdgeBound_logVolume_hull_le_ofReal W himgθ) hθ0 hqneg
          ipl she apt hipl hshe hapt)) :=
  iqHullCor312Conclusion W.toIQHullLogVolumeInterface pt hpt data hvalue hw q θ
    hq (iqHullEdgeBound_logVolume_hull_le_ofReal W himgθ) hθ0 hqneg ipl she apt
    hipl hshe hapt

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the R9-(c)/(d) attack round: the multiplicative-action /
`dot-mu` decomposition interface with its derived laws and value-layer binding,
the max-stability dichotomy on the hull (unconditional negative at positive
log-degree, contractive-regime positive, exact characterization), the sharp
value-layer characterization of R9, and the image-set-level theta-slot
re-supply for the certificate consumers. -/
def cardHullRealEdgeNormalizationDichotomy : Obligation :=
  { id := "IUT-III.corollary-3.12-card-hullreal-edge-normalization-dichotomy"
    source :=
      "IUT III, Corollary 3.12 proof, Steps (xi-d)-(xi-f): corpus lines " ++
        "10381-10414 (possible images; 1,circ U compactness; negativity of " ++
        "-|log(Theta)|), 10843-10863 (Theta x mu-LGP-link identification; " ++
        "log-Kummer correspondence in the 1-column; tensor packets of " ++
        "log-shells); [AbsTopIII] Proposition 5.7, (i), (b) (dot-mu " ++
        "decomposition), Corollary 5.10 (normalized log-volume), via the " ++
        "carrier-line report section 14; Remark 3.9.5, (i)-(ii)"
    status := VerificationStatus.interface
    note :=
      "R9-(c)/(d) round. (c) interface structure " ++
        "LogVolumeScaleDecomposition with normalization, decomposition, " ++
        "dot-mu laws (factor of the unit-region translate, unit, " ++
        "additivity, invariance, nonpositivity along products/powers) and " ++
        "value-layer binding (sourceMulImage bound transfer, set-level " ++
        "decomposition bound). (d) max-stability dichotomy: on the hull, " ++
        "vol(x*y) <= max(vol x)(vol y) iff every hull point is a " ++
        "contraction; the negative direction is unconditional (square " ++
        "witness, no degree-faithfulness premise). Sharper: at the value " ++
        "layer, R9 iff every hull point (equivalently every generator) has " ++
        "nonpositive log-degree; R9 body still unproved. Theta-slot " ++
        "re-supply lemmas for CertificateHullWiring lines 155/204 " ++
        "(image-set-level bound). NOT proved: existence of a " ++
        "positive-degree hull point in any concrete instance (the dichotomy " ++
        "is conditional); instantiation of the multiplicative structure on " ++
        "the paper carrier; R9 body. Report section 19."
    dependsOn :=
      [ "IUT-III.corollary-3.12-card-hullreal-edge-normalization-reduction",
        "IUT-III.corollary-3.12-card-hullreal-geometry-reduction" ] }

end LeanFormal.IUT.Audit
