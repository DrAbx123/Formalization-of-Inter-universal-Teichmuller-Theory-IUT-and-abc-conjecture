import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealSignedLogVolume

/-!
# Card-HULLREAL: reduction of the via-images hull-volume identity

Task `hunit-epsilon-transfer-20261016`, geometry-reduction package (report
`logs/coordination/hunit-epsilon-transfer-20261016.md`, section 17).  The
signed wrapper package (`CardHullRealSignedLogVolume.lean`) reduced the corpus
(xi-f) comparison to the single value-layer identity; this file performs the
requested attack round on that identity

`sourceHullVolume v R n = sourceSetVolume v (possibleThetaPilotImageSet v R n)`

(the hull log-volume equals the image-union log-volume), which is the
value-layer form of:

* (xi-d), III:10843-10848: `-|log(Theta)|` is the (negative) log-volume of
  `1,circ U`, computed via the possible images; and
* III:990-993, 1051-1053: the computation of the log-volume of the
  holomorphic hull of the union of possible images of the Theta-pilot object
  necessarily amounts to a computation (of an upper bound) of `|log(q)|`.

What is proved here (unconditional unless a hypothesis is displayed):

* `sourceScalingUnits_subset_sourceHolomorphicHull` and
  `sourceHolomorphicHull_eq_closure`: the hull is exactly the submonoid
  closure of the possible images together with the scaling units -- the
  generator characterization that turns the identity into a finite-product
  statement (Remark 3.9.5, (i)-(ii): hull as the least `lambda . O` region).
* `sourcePointVolume_mul_le`: subadditivity of the point log-volume under
  multiplication (the volume of a product is at most the sum of the volumes),
  from additivity of the local log-degrees and `ofReal` subadditivity.
* The reduction chain (`sourceHullVolume_eq_imageVolume_iff`,
  `sourceHullVolume_le_imageVolume_iff_forall_pointVolume_le`,
  `..._iff_forall_pointVolume_le_labelSup`): the identity is equivalent to
  the single inequality `hull <= image`, which is equivalent to the pointwise
  check over all hull points, in the finite-label (vertex) form.
* Necessary conditions and failure certificates
  (`sourcePointVolume_imageProduct_le_of_hullVolume_le_imageVolume`,
  `sourcePointVolume_scaling_le_of_hullVolume_le_imageVolume`,
  `not_sourceHullVolume_le_imageVolume_of_pointVolume_gt` and its
  product/scaling instances): every product of images and every scaling in
  the hull must stay below the image volume; any single violation refutes the
  identity outright.
* Sufficient reductions: a candidate hull with controlled volume suffices
  (`sourceHullVolume_le_imageVolume_of_candidate`); and if every generator
  (image or scaling) has nonpositive local log-degree-sum, the identity holds
  degenerately (`..._of_generator_nonpos`: all hull volumes vanish; this is
  the contractive/neutral regime of IUT III Corollary 3.12, not a corpus
  claim at this layer).
* Signed face (`sourceSignedImage_le_signedHull_iff_hullVolume_le_imageVolume`,
  `sourceSignedImageComparison_iff_hullVolume_eq_imageVolume`,
  `sourceSignedImage_eq_signedHull_of_corpusDirection`): under finiteness, the
  corpus (xi-f) direction, the via-images identity, and the single inequality
  are all equivalent; the antisymmetric closure of the corpus direction with
  the tree direction is the identity.

Not proved here: the inequality `sourceHullVolume <= image volume` itself.  It
is not a formal consequence of the present data -- by the closure
characterization it is a statement about all finite products of images and
scalings, whose volumes are sums of generator volumes; the failure
certificates above show that any positive-degree generator exceeding the edge
sup refutes it.  The decomposition list and the required arithmetic geometry
are recorded in report section 17 (items R9, R10).

Paper route vs. our route: the corpus obtains `hull = -|log(Theta)|` computed
via the possible images from the actual `1,circ U`/log-shell/Theta x mu-LGP-
link apparatus (III:1042-1058, 10843-10898); the value layer has no such
object, so this file reduces the identity to machine-checked structural and
pointwise forms and records the remaining arithmetic input as a card.  No
degree-faithful premise is introduced anywhere.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

noncomputable section

universe ua uv upi umon ui

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. Generator characterization of the hull -/

/-- Every scaling unit lies in the source holomorphic hull: `s = s * 1` and
the hull is stable under multiplication by scalings and contains `1`. -/
theorem sourceScalingUnits_subset_sourceHolomorphicHull (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceScalingUnits v ⊆ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) := by
  intro s hs
  have h : s * 1 ∈ I.sourceHolomorphicHull v R n :=
    I.sourceHolomorphicHull_scaling_mem v R n hs
      (I.sourceHolomorphicHull_one_mem v R n)
  simpa using h

/-- **Generator characterization.**  The source holomorphic hull is exactly
the submonoid closure of the possible theta-pilot images together with the
scaling units: every hull point is a finite product of image points and
scaling units, and every such product lies in the hull (Remark 3.9.5,
(i)-(ii), at the value-monoid level). -/
theorem sourceHolomorphicHull_eq_closure (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceHolomorphicHull v R n =
      Submonoid.closure (I.possibleThetaPilotImageSet v R n ∪ I.sourceScalingUnits v) := by
  apply le_antisymm
  · refine I.sourceHolomorphicHull_le v R n ?_ ?_
    · intro s hs x hx
      exact Submonoid.mul_mem _ (Submonoid.subset_closure (Or.inr hs)) hx
    · intro x hx
      exact Submonoid.subset_closure (Or.inl hx)
  · refine Submonoid.closure_le.mpr ?_
    intro x hx
    rcases hx with hx | hx
    · exact I.possibleThetaPilotImage_subset_sourceHolomorphicHull v R n hx
    · exact sourceScalingUnits_subset_sourceHolomorphicHull I v R n hx

/-! ## 2. Volume arithmetic of the value layer -/

/-- Subadditivity of the point log-volume under multiplication: the volume of
a product is at most the sum of the volumes, since the local log-degrees are
additive (`sourceLocalLogDegree_mul`) and `ofReal` is subadditive. -/
theorem sourcePointVolume_mul_le (v : V) (x y : I.ThetaPilotPoint v) :
    I.sourcePointVolume v (x * y) ≤
      I.sourcePointVolume v x + I.sourcePointVolume v y := by
  unfold sourcePointVolume
  rw [I.sourceLocalLogDegree_mul]
  exact ENNReal.ofReal_add_le

/-- Every point of the hull has point volume at most the hull volume (the
defining supremum). -/
theorem sourcePointVolume_le_sourceHullVolume_of_mem (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    {x : I.ThetaPilotPoint v} (hx : x ∈ I.sourceHolomorphicHull v R n) :
    I.sourcePointVolume v x ≤ I.sourceHullVolume v R n := by
  unfold sourceHullVolume sourceSetVolume
  exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)

/-! ## 3. The identity reduced to one inequality and to pointwise checks -/

/-- **Antisymmetric collapse (card 3).**  Given the tree direction
`image <= hull` (`sourceHullVolume_ge_imageVolume`), the via-images identity
is equivalent to the single remaining inequality `hull <= image`.  This is
the precise content of the antisymmetric step: nothing but one inequality
remains. -/
theorem sourceHullVolume_eq_imageVolume_iff (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceHullVolume v R n =
        I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) ↔
      I.sourceHullVolume v R n ≤
        I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) :=
  ⟨fun h => h.le, fun h => le_antisymm h (I.sourceHullVolume_ge_imageVolume v R n)⟩

/-- **Pointwise reduction.**  The remaining inequality holds exactly when
every hull point has point volume at most the image-union volume. -/
theorem sourceHullVolume_le_imageVolume_iff_forall_pointVolume_le (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceHullVolume v R n ≤
        I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) ↔
      ∀ x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        I.sourcePointVolume v x ≤
          I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) := by
  unfold sourceHullVolume sourceSetVolume
  constructor
  · intro h x hx
    exact le_trans (sourcePointVolume_le_sourceHullVolume_of_mem I v R n hx) h
  · intro h
    exact iSup₂_le fun x hx => h x hx

/-- **Vertex (finite-label) form.**  The image-union volume is the supremum
over the finitely many signed labels (Card B,
`sourceSetVolume_possibleImageSet_eq_labelSup`), so the remaining inequality
is exactly the check that every hull point has point volume at most the label
supremum of local log-degrees. -/
theorem sourceHullVolume_le_imageVolume_iff_forall_pointVolume_le_labelSup
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceHullVolume v R n ≤
        ⨆ j : SignedLabel l.value,
          ENNReal.ofReal
            (I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j)) ↔
      ∀ x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        I.sourcePointVolume v x ≤
          ⨆ j : SignedLabel l.value,
            ENNReal.ofReal
              (I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j)) := by
  rw [← sourceSetVolume_possibleImageSet_eq_labelSup (I := I) v R n]
  exact sourceHullVolume_le_imageVolume_iff_forall_pointVolume_le I v R n

/-! ## 4. Necessary conditions and failure certificates -/

/-- **Failure certificate (general form).**  A single hull point whose point
volume exceeds the image-union volume refutes the remaining inequality (and
hence the identity). -/
theorem not_sourceHullVolume_le_imageVolume_of_pointVolume_gt (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    {z : I.ThetaPilotPoint v} (hz : z ∈ I.sourceHolomorphicHull v R n)
    (hgt : I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) <
      I.sourcePointVolume v z) :
    ¬ I.sourceHullVolume v R n ≤
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) :=
  fun hle => not_le_of_gt
    (lt_of_lt_of_le hgt (sourcePointVolume_le_sourceHullVolume_of_mem I v R n hz)) hle

/-- **Failure certificate (image products).**  A product of two possible
images is a hull point, so if its point volume exceeds the image-union volume
the identity fails. -/
theorem not_sourceHullVolume_le_imageVolume_of_imageProductVolume_gt (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (j j' : SignedLabel l.value)
    (hgt : I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) <
      I.sourcePointVolume v (I.sourceThetaPilotPoint v R n j *
        I.sourceThetaPilotPoint v R n j')) :
    ¬ I.sourceHullVolume v R n ≤
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) :=
  not_sourceHullVolume_le_imageVolume_of_pointVolume_gt I v R n
    (I.sourceHolomorphicHull_mul_mem v R n
      (I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n j)
      (I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n j'))
    hgt

/-- **Failure certificate (scalings).**  Every scaling unit is a hull point,
so a scaling whose point volume exceeds the image-union volume refutes the
identity. -/
theorem not_sourceHullVolume_le_imageVolume_of_scalingVolume_gt (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    {s : I.ThetaPilotPoint v} (hs : s ∈ I.sourceScalingUnits v)
    (hgt : I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) <
      I.sourcePointVolume v s) :
    ¬ I.sourceHullVolume v R n ≤
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) :=
  not_sourceHullVolume_le_imageVolume_of_pointVolume_gt I v R n
    (sourceScalingUnits_subset_sourceHolomorphicHull I v R n hs) hgt

/-- **Necessary condition (image products).**  If the remaining inequality
holds, then every product of two possible images has point volume at most the
image-union volume. -/
theorem sourcePointVolume_imageProduct_le_of_hullVolume_le_imageVolume
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hV : I.sourceHullVolume v R n ≤
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n))
    (j j' : SignedLabel l.value) :
    I.sourcePointVolume v (I.sourceThetaPilotPoint v R n j *
        I.sourceThetaPilotPoint v R n j') ≤
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) :=
  le_trans
    (sourcePointVolume_le_sourceHullVolume_of_mem I v R n
      (I.sourceHolomorphicHull_mul_mem v R n
        (I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n j)
        (I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n j')))
    hV

/-- **Necessary condition (scalings).**  If the remaining inequality holds,
then every scaling unit has point volume at most the image-union volume. -/
theorem sourcePointVolume_scaling_le_of_hullVolume_le_imageVolume
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hV : I.sourceHullVolume v R n ≤
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n))
    {s : I.ThetaPilotPoint v} (hs : s ∈ I.sourceScalingUnits v) :
    I.sourcePointVolume v s ≤
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) :=
  le_trans
    (sourcePointVolume_le_sourceHullVolume_of_mem I v R n
      (sourceScalingUnits_subset_sourceHolomorphicHull I v R n hs))
    hV

/-! ## 5. Sufficient reductions -/

/-- **Sufficient reduction (candidate hull with controlled volume).**  If any
candidate hull containing the images has set-volume at most the image-union
volume, the remaining inequality holds: the source hull is contained in every
candidate hull. -/
theorem sourceHullVolume_le_imageVolume_of_candidate (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    {H : Submonoid (I.ThetaPilotPoint v)}
    (hH : CandidateHull (I.sourceScalingUnits v) H)
    (hsub : I.possibleThetaPilotImageSet v R n ⊆
      (H : Set (I.ThetaPilotPoint v)))
    (hvol : I.sourceSetVolume v (H : Set (I.ThetaPilotPoint v)) ≤
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)) :
    I.sourceHullVolume v R n ≤
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) :=
  le_trans
    (sourceSetVolume_mono (I := I) v
      (fun x hx => I.sourceHolomorphicHull_le v R n hH hsub hx))
    hvol

/-- **Degree propagation through the closure.**  If every generator (possible
image or scaling unit) has nonpositive local log-degree-sum, then so does
every hull point, by the closure characterization and additivity of the
log-degree under multiplication. -/
theorem sourceLocalLogDegree_le_zero_of_mem_sourceHolomorphicHull
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (himg : ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ 0)
    (hscal : ∀ s ∈ I.sourceScalingUnits v, I.sourceLocalLogDegree v s ≤ 0) :
    ∀ z ∈ I.sourceHolomorphicHull v R n, I.sourceLocalLogDegree v z ≤ 0 := by
  intro z hz
  rw [sourceHolomorphicHull_eq_closure I v R n] at hz
  refine Submonoid.closure_induction
    (motive := fun z _ => I.sourceLocalLogDegree v z ≤ 0) ?_ ?_ ?_ hz
  · intro x hx
    rcases hx with hx | hx
    · obtain ⟨j, rfl⟩ := (I.mem_possibleThetaPilotImageSet_iff v R n x).mp hx
      exact himg j
    · exact hscal x hx
  · exact le_of_eq (I.sourceLocalLogDegree_one v)
  · intro x y _hx _hy ihx ihy
    rw [I.sourceLocalLogDegree_mul]
    linarith

/-- **Sufficient reduction (contractive/neutral generator regime).**  If
every generator has nonpositive local log-degree-sum, the remaining
inequality holds: every hull point has point volume `0`, hence volume at most
the image-union volume.  In this regime the identity holds degenerately (all
hull volumes vanish); the nondegenerate content of the identity is exactly
the failure of generator nonpositivity, which is the arithmetic input
recorded in report section 17 (items R9, R10). -/
theorem sourceHullVolume_le_imageVolume_of_generator_nonpos (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (himg : ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ 0)
    (hscal : ∀ s ∈ I.sourceScalingUnits v, I.sourceLocalLogDegree v s ≤ 0) :
    I.sourceHullVolume v R n ≤
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) := by
  rw [sourceHullVolume_le_imageVolume_iff_forall_pointVolume_le]
  intro z hz
  have hz0 : I.sourceLocalLogDegree v z ≤ 0 :=
    sourceLocalLogDegree_le_zero_of_mem_sourceHolomorphicHull
      I v R n himg hscal z hz
  have hvol : I.sourcePointVolume v z = 0 := ENNReal.ofReal_eq_zero.mpr hz0
  rw [hvol]
  exact zero_le

/-! ## 6. Signed face: the corpus direction and the identity are equivalent -/

/-- **Signed equivalent of the single inequality.**  Under finiteness, the
corpus (xi-f) signed direction `-|log(q)| <= -|log(Theta)|` holds exactly
when the remaining inequality `hull <= image` holds. -/
theorem sourceSignedImage_le_signedHull_iff_hullVolume_le_imageVolume
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) :
    I.sourceSignedImageLogVolume v R n ≤ I.sourceSignedHullLogVolume v R n ↔
      I.sourceHullVolume v R n ≤
        I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) := by
  constructor
  · intro h
    have h1 : I.sourceRealHullVolume v R n ≤
        (I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)).toReal := by
      unfold sourceSignedImageLogVolume sourceSignedHullLogVolume
        sourceRealHullVolume at h
      exact neg_le_neg_iff.mp h
    have hfinImg : I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) < ⊤ :=
      lt_of_le_of_lt (I.sourceHullVolume_ge_imageVolume v R n) hfin
    calc I.sourceHullVolume v R n =
          ENNReal.ofReal (I.sourceRealHullVolume v R n) :=
        I.sourceHullVolume_eq_ofReal v R n hfin
      _ ≤ ENNReal.ofReal
            ((I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)).toReal) :=
        ENNReal.ofReal_le_ofReal h1
      _ = I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) :=
        ENNReal.ofReal_toReal (ne_top_of_lt hfinImg)
  · intro h
    have hfinImg : I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) < ⊤ :=
      lt_of_le_of_lt (I.sourceHullVolume_ge_imageVolume v R n) hfin
    have h1 : I.sourceRealHullVolume v R n ≤
        (I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)).toReal :=
      ENNReal.toReal_mono (ne_top_of_lt hfinImg) h
    unfold sourceSignedImageLogVolume sourceSignedHullLogVolume sourceRealHullVolume
    exact neg_le_neg_iff.mpr h1

/-- **Signed comparison = via-images identity.**  Under finiteness, the
corpus (xi-f) signed direction is equivalent to the identity
`sourceHullVolume = image volume` -- the (xi-d) "computed via the possible
images" statement.  This closes the reduction chain of the signed package in
the `ENNReal` layer. -/
theorem sourceSignedImageComparison_iff_hullVolume_eq_imageVolume
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) :
    I.sourceSignedImageLogVolume v R n ≤ I.sourceSignedHullLogVolume v R n ↔
      I.sourceHullVolume v R n =
        I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) := by
  constructor
  · intro h
    exact sourceHullVolume_eq_imageVolume_of_signedImageComparison I v R n hfin h
  · intro h
    exact sourceSignedImageComparison_of_hullVolume_eq_imageVolume I v R n h

/-- **Antisymmetric closure (card 3, final form).**  The corpus direction
together with the tree direction gives the signed equality: on the signed
surface the comparison and the identity coincide. -/
theorem sourceSignedImage_eq_signedHull_of_corpusDirection (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤)
    (h : I.sourceSignedImageLogVolume v R n ≤
      I.sourceSignedHullLogVolume v R n) :
    I.sourceSignedImageLogVolume v R n = I.sourceSignedHullLogVolume v R n :=
  le_antisymm h
    (I.sourceSignedHullLogVolume_le_sourceSignedImageLogVolume v R n hfin)

end OriginalInput
end Theorem311Source

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the Card-HULLREAL geometry-reduction round on the
via-images identity `sourceHullVolume = image volume`: generator
characterization of the hull (closure form), volume subadditivity, the
antisymmetric collapse of the identity to the single inequality
`hull <= image`, its pointwise and finite-vertex forms, necessary conditions
and failure certificates, and sufficient reductions (candidate hull;
contractive generator regime).  The inequality itself remains unproved: the
value layer does not contain the arithmetic input controlling positive-degree
generators; the decomposition list and the `q`-region spec sheet are in
report section 17. -/
def cardHullRealGeometryReduction : Obligation :=
  { id := "IUT-III.corollary-3.12-card-hullreal-geometry-reduction"
    source :=
      "IUT III, Corollary 3.12 proof, Steps (xi-d)-(xi-f) (III:10843-10898); " ++
        "Remark 3.9.5, (i)-(ii) (hull as least lambda . O region)"
    status := VerificationStatus.interface
    note :=
      "Reduction round on sourceHullVolume = possibleThetaPilotImageSet " ++
        "volume. PROVED: hull = submonoid closure of images + scaling units " ++
        "(sourceHolomorphicHull_eq_closure); point-volume subadditivity under " ++
        "multiplication; identity <=> single inequality <=> pointwise hull " ++
        "check <=> finite-label form; necessary conditions (image products, " ++
        "scalings) and single-point failure certificates; sufficient " ++
        "reductions (candidate hull with controlled volume; contractive " ++
        "generator regime, degenerate). Signed face: under finiteness the " ++
        "corpus (xi-f) direction, the identity and the inequality are " ++
        "equivalent (sourceSignedImageComparison_iff_hullVolume_eq_imageVolume). " ++
        "NOT proved: hull <= image itself -- a statement about all finite " ++
        "products of images and scalings (volumes add), falsified by any " ++
        "positive-degree generator exceeding the edge sup; requires the " ++
        "arithmetic geometry of 1,circ U / log-shells (card R9/R10, report " ++
        "section 17)."
    dependsOn :=
      [ "IUT-III.corollary-3.12-card-hullreal-signed-log-volume"
      , "IUT-III.corollary-3.12-source-image-hull-volume"
      , "IUT-III.corollary-3.12-card-hullreal-geometry-gap-cards"
      , "IUT-III.source-procession-stepXI-xif-inclusion" ] }

end LeanFormal.IUT.Audit