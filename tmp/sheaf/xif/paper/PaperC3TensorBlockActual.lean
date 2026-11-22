import tmp.sheaf.xif.paper.PaperC3TensorGeometryActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalAbsorption
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceHolomorphicIntegralClosure
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology
import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv

/-!
# Actual nondegenerate tensor block and true lambda-O hull

The tensor block uses one actual source completion place per source index,

  Block = ArithmeticTensorTupleBlock (fun v _ => G.place v) (fun _ => ()),

and the possible Theta image comes from the actual q units of the completion
valued source geometry G.qUnit.  The hull is NOT a closure: it is the smallest
intersection of actual nonzero lambda-scaled unit regions

  lambda * O

containing the image.  The actual relation to the canonical arithmetic hull is
proved whenever that canonical hull is itself a nonzero scaled unit region
containing the image.

The exact missing source data are recorded as gaps (place injectivity,
existence of a lambda-O candidate, and the lambda-O scaling relation).
No constant place, closure-as-hull, fake image, or fake scaling is used.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorGeometryActual
open MeasureTheory

universe u

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type} [Fintype V]
variable {l : PrimeGeFive}
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- The actual tensor block with one indexed source place per factor. -/
abbrev Block : Type :=
  ArithmeticTensorTupleBlock (fun v (_ : Unit) => G.place v) (fun _ => ())

/-- The actual tensor place is the source place at v. -/
theorem paperTensorPlaces_apply (v : V) :
    paperTensorPlaces (G := G) (l := l) v (paperTensorTuple (V := V) v) =
      G.place v := rfl

/-- Actual holomorphic lattice of the tensor block. -/
noncomputable abbrev paperHolomorphicLattice : Submodule ℤ_[p] (Block (G := G)) :=
  arithmeticTupleHolomorphicLattice (fun v (_ : Unit) => G.place v) (fun _ => ())

/-- Actual canonical unit region O. -/
noncomputable abbrev paperUnitReference : Set (Block (G := G)) :=
  arithmeticTupleCanonicalUnitReference (fun v (_ : Unit) => G.place v) (fun _ => ())

/-- Actual canonical arithmetic hull of O. -/
noncomputable abbrev paperCanonicalHull : Set (Block (G := G)) :=
  arithmeticTupleCanonicalHull (fun v (_ : Unit) => G.place v) (fun _ => ())

/-- CAUTION: this is the qVFamily q-parameter power q_v^(j^2) in the completion
tensor block, NOT the paper Theta value.  The paper Theta value is the
2l-th-root value q_v^(j^2) with q_v = q^(1/2l), constructed in
PaperC3RootThetaHullActual/PaperC3ThetaRootActual on the algebraic-closure
Kummer extension. -/
noncomputable def paperQParameterImagePoint
    (j : SignedLabel l.value) : Block (G := G) :=
  finitePadicTensorTprod (p := p)
    (fun v => CommonPrimeCompletion (G.place v))
    (fun v => (((G.qUnit v : G.valueCarrier v) ^
      (gaussExponent j.1).toNat) : CommonPrimeCompletion (G.place v)))

/-- The actual finite possible Theta image set. -/
noncomputable def paperQParameterImageSet : Set (Block (G := G)) :=
  Set.range (paperQParameterImagePoint (G := G) (l := l))

/-- Actual nonzero lambda-O scaled unit region. -/
noncomputable def paperScaledRegion
    (lam : Block (G := G)) : Set (Block (G := G)) :=
  {x | ∃ o ∈ paperUnitReference (G := G), x = lam * o}

/-- The unit scaling 1 * O is exactly O. -/
theorem paperScaledRegion_one :
    paperScaledRegion (G := G) (1 : Block (G := G)) =
      paperUnitReference (G := G) := by
  ext x
  constructor
  · rintro ⟨o, ho, rfl⟩
    simpa using ho
  · intro hx
    exact ⟨x, hx, by rw [one_mul]⟩

/-- Actual candidate lambda-O hulls containing the Theta image. -/
def paperCandidateHulls : Set (Set (Block (G := G))) :=
  {H | ∃ lam : Block (G := G), lam ≠ 0 ∧
    H = paperScaledRegion (G := G) lam ∧
    paperQParameterImageSet (G := G) (l := l) ⊆ H}

/-- The actual smallest lambda-O hull containing the Theta image: the
intersection of all actual nonzero scaled regions containing the image.
This is not a closure. -/
noncomputable def paperQParameterHull : Set (Block (G := G)) :=
  ⋂ H ∈ paperCandidateHulls (G := G) (l := l), H

/-- The actual Theta image is contained in the actual lambda-O hull. -/
theorem paperQParameterImageSet_subset_hull :
    paperQParameterImageSet (G := G) (l := l) ⊆
      paperQParameterHull (G := G) (l := l) := by
  intro x hx
  simp only [paperQParameterHull, Set.mem_iInter]
  intro H hH
  rcases hH with ⟨lam, hne, hEq, hsub⟩
  exact hsub hx

/-- The actual lambda-O hull is contained in every actual candidate. -/
theorem paperQParameterHull_subset_candidate
    (H : Set (Block (G := G)))
    (hH : H ∈ paperCandidateHulls (G := G) (l := l)) :
    paperQParameterHull (G := G) (l := l) ⊆ H := by
  intro x hx
  have hx' : ∀ H : Set (Block (G := G)),
      H ∈ paperCandidateHulls (G := G) (l := l) → x ∈ H := by
    simpa only [paperQParameterHull, Set.mem_iInter] using hx
  exact hx' H hH

/-- Equality of the actual lambda-O hull with the candidate intersection. -/
theorem paperQParameterHull_eq_iInter :
    paperQParameterHull (G := G) (l := l) =
      ⋂ H ∈ paperCandidateHulls (G := G) (l := l), H := rfl

/-- The lambda-O hull is contained in the scaled region of any actual
nonzero candidate. -/
theorem paperQParameterHull_subset_scaledRegion_of_candidate
    (lam : Block (G := G)) (hne : lam ≠ 0)
    (hsub : paperQParameterImageSet (G := G) (l := l) ⊆
      paperScaledRegion (G := G) lam) :
    paperQParameterHull (G := G) (l := l) ⊆
      paperScaledRegion (G := G) lam := by
  apply paperQParameterHull_subset_candidate (G := G) (l := l)
  exact ⟨lam, hne, rfl, hsub⟩

/-- If the canonical arithmetic hull is an actual nonzero scaled unit region
containing the image, the lambda-O hull is contained in it. -/
theorem paperQParameterHull_subset_canonicalHull_of_candidate
    (lam : Block (G := G)) (hne : lam ≠ 0)
    (hcanon : paperCanonicalHull (G := G) = paperScaledRegion (G := G) lam)
    (hsub : paperQParameterImageSet (G := G) (l := l) ⊆
      paperCanonicalHull (G := G)) :
    paperQParameterHull (G := G) (l := l) ⊆ paperCanonicalHull (G := G) := by
  rw [hcanon]
  apply paperQParameterHull_subset_scaledRegion_of_candidate (G := G) (l := l)
  · exact hne
  · simpa only [hcanon] using hsub

/-- Exact missing source data: place injectivity, existence of an actual
lambda-O candidate, and the actual lambda-O scaling relation. -/
structure PaperC3TensorSourceGap : Type where
  places_injective : Prop
  lambdaOCandidate_exists : Prop
  lambdaOScalingRelation : Prop

/-- Exact missing source object. -/
def PaperC3TensorSourceGapRequired : Prop :=
  Nonempty PaperC3TensorSourceGap

/-- Actual tensor block/image/hull data. -/
structure PaperC3TensorBlockData where
  imageSet : Set (Block (G := G))
  imageSet_eq : imageSet = paperQParameterImageSet (G := G) (l := l)
  image_finite : imageSet.Finite
  hull : Set (Block (G := G))
  hull_eq : hull = paperQParameterHull (G := G) (l := l)
  image_subset_hull : imageSet ⊆ hull
  holomorphicLattice : Submodule ℤ_[p] (Block (G := G))
  holomorphicLattice_eq : holomorphicLattice = paperHolomorphicLattice (G := G)

/-- Actual tensor block data. -/
noncomputable def paperC3TensorBlockData :
    PaperC3TensorBlockData (G := G) (l := l) where
  imageSet := paperQParameterImageSet (G := G) (l := l)
  imageSet_eq := rfl
  image_finite := Set.finite_range _
  hull := paperQParameterHull (G := G) (l := l)
  hull_eq := rfl
  image_subset_hull := paperQParameterImageSet_subset_hull (G := G) (l := l)
  holomorphicLattice := paperHolomorphicLattice (G := G)
  holomorphicLattice_eq := rfl


/-- Actual Ind2 possible-image action: precompose the image family with a
signed-label permutation. -/
noncomputable def paperInd2ImageSet
    (tau : Equiv.Perm (SignedLabel l.value)) : Set (Block (G := G)) :=
  Set.range (fun j => paperQParameterImagePoint (G := G) (l := l) (tau j))

/-- Actual Ind2 possible-image union over all signed-label permutations. -/
noncomputable def paperInd2ImageUnion : Set (Block (G := G)) :=
  ⋃ tau : Equiv.Perm (SignedLabel l.value),
    paperInd2ImageSet (G := G) (l := l) tau

/-- The Ind2 union is contained in the finite image set. -/
theorem paperInd2ImageUnion_subset_imageSet :
    paperInd2ImageUnion (G := G) (l := l) ⊆
      paperQParameterImageSet (G := G) (l := l) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨tau, hx⟩
  rcases hx with ⟨j, rfl⟩
  exact ⟨tau j, rfl⟩

/-- The finite image set is contained in the Ind2 union. -/
theorem imageSet_subset_paperInd2ImageUnion :
    paperQParameterImageSet (G := G) (l := l) ⊆
      paperInd2ImageUnion (G := G) (l := l) := by
  intro x hx
  rcases hx with ⟨j, rfl⟩
  refine Set.mem_iUnion.mpr ⟨Equiv.refl _, ?_⟩
  exact ⟨j, rfl⟩

/-- Actual Ind2 possible-image union is exactly the original finite image set. -/
theorem paperInd2ImageUnion_eq_imageSet :
    paperInd2ImageUnion (G := G) (l := l) =
      paperQParameterImageSet (G := G) (l := l) :=
  Set.Subset.antisymm
    (paperInd2ImageUnion_subset_imageSet (G := G) (l := l))
    (imageSet_subset_paperInd2ImageUnion (G := G) (l := l))

/-- The Ind2 union is contained in the actual lambda-O hull. -/
theorem paperInd2ImageUnion_subset_paperQParameterHull :
    paperInd2ImageUnion (G := G) (l := l) ⊆
      paperQParameterHull (G := G) (l := l) := by
  rw [paperInd2ImageUnion_eq_imageSet (G := G) (l := l)]
  exact paperQParameterImageSet_subset_hull (G := G) (l := l)

/-- Exact missing Ind1/Ind3/Kummer possible-image maps on the tensor block.
Ind2 is actual above; the other three actions live on different carriers and
have no supplied actual map to this Block. -/
structure PaperIndImageActionGap : Type where
  ind1_block_action : Prop
  ind3_stage_to_block : Prop
  kummer_action_on_block : Prop
  ind1_union_eq_image : Prop
  ind3_union_eq_image : Prop
  kummer_union_eq_image : Prop

/-- Exact missing Ind action/image object. -/
def PaperIndImageActionGapRequired : Prop :=
  Nonempty PaperIndImageActionGap

/-- Actual Ind2 image-union data. -/
structure PaperInd2ImageUnionData where
  imageSet : Set (Block (G := G))
  imageSet_eq : imageSet = paperInd2ImageUnion (G := G) (l := l)
  baseImage_eq : imageSet = paperQParameterImageSet (G := G) (l := l)
  image_subset_hull : imageSet ⊆ paperQParameterHull (G := G) (l := l)

/-- Actual Ind2 image-union data. -/
noncomputable def paperInd2ImageUnionData :
    PaperInd2ImageUnionData (G := G) (l := l) where
  imageSet := paperInd2ImageUnion (G := G) (l := l)
  imageSet_eq := rfl
  baseImage_eq := paperInd2ImageUnion_eq_imageSet (G := G) (l := l)
  image_subset_hull := paperInd2ImageUnion_subset_paperQParameterHull (G := G) (l := l)

/-- Actual normalized log-volume of the lambda-O hull, once a measure is chosen. -/
noncomputable def paperQParameterHullNormalizedLog
    [MeasurableSpace (Block (G := G))]
    (mu : Measure (Block (G := G))) : Real :=
  arithmeticTupleNormalizedLogVolume
    (fun v (_ : Unit) => G.place v) (fun _ => ()) mu
    (paperQParameterHull (G := G) (l := l))

/-- Exact missing hull Haar/mu_log data: an actual lambda-O candidate equal to
the hull, its positive finite Haar, and the normalized-log formula. -/
structure PaperQParameterHullHaarGap
    [MeasurableSpace (Block (G := G))]
    (mu : Measure (Block (G := G))) : Type where
  candidate_exists : Prop
  hull_eq_candidate : Prop
  hull_measure_pos : Prop
  hull_measure_lt_top : Prop
  hullLog_eq_normalizedLog : Prop

/-- Exact missing hull Haar/mu_log object. -/
def PaperQParameterHullHaarGapRequired
    [MeasurableSpace (Block (G := G))]
    (mu : Measure (Block (G := G))) : Prop :=
  Nonempty (PaperQParameterHullHaarGap (G := G) (l := l) mu)


/-- Under the norm condition for the actual q units, every possible Theta
image point is integral over Z_p, hence lies in the canonical unit reference O. -/
theorem paperQParameterImagePoint_mem_unitReference_of_norm_le_one
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1)
    (j : SignedLabel l.value) :
    paperQParameterImagePoint (G := G) (l := l) j ∈
      paperUnitReference (G := G) := by
  classical
  let n : Nat := (gaussExponent j.1).toNat
  let u : (v : V) → CommonPrimeCompletion (G.place v) :=
    fun v => (((G.qUnit v : G.valueCarrier v) ^ n) :
      CommonPrimeCompletion (G.place v))
  have hu : ∀ v : V, ‖u v‖ ≤ 1 := by
    intro v
    dsimp only [u]
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hq v)
  have hint : IsIntegral ℤ_[p]
      (arithmeticTupleTprod (fun v (_ : Unit) => G.place v)
        (fun _ => ()) u) :=
    isIntegral_arithmeticTupleTprod_of_norm_le_one
      (fun v (_ : Unit) => G.place v) (fun _ => ()) u hu
  rw [paperUnitReference, arithmeticTupleCanonicalUnitReference_eq_integralClosure]
  have hmem : arithmeticTupleTprod (fun v (_ : Unit) => G.place v)
      (fun _ => ()) u ∈
      (integralClosure ℤ_[p] (Block (G := G)) : Set (Block (G := G))) :=
    (mem_integralClosure_iff ℤ_[p] (Block (G := G))).mpr hint
  simpa only [u, n, paperQParameterImagePoint] using hmem

/-- Under the norm condition, the whole possible Theta image is contained in
the canonical unit reference O. -/
theorem paperQParameterImageSet_subset_unitReference_of_norm_le_one
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    paperQParameterImageSet (G := G) (l := l) ⊆
      paperUnitReference (G := G) := by
  rintro x ⟨j, rfl⟩
  exact paperQParameterImagePoint_mem_unitReference_of_norm_le_one
    (G := G) (l := l) hq j

/-- The unit lambda = 1 candidate O is an actual lambda-O candidate containing
the image, under the norm condition. -/
theorem paperUnitReference_mem_candidateHulls_of_norm_le_one
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    paperUnitReference (G := G) ∈
      paperCandidateHulls (G := G) (l := l) := by
  refine ⟨1, one_ne_zero, ?_, ?_⟩
  · exact (paperScaledRegion_one (G := G)).symm
  · exact paperQParameterImageSet_subset_unitReference_of_norm_le_one
      (G := G) (l := l) hq

/-- Under the norm condition, the lambda-O hull is contained in O. -/
theorem paperQParameterHull_subset_unitReference_of_norm_le_one
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    paperQParameterHull (G := G) (l := l) ⊆ paperUnitReference (G := G) :=
  paperQParameterHull_subset_candidate (G := G) (l := l)
    (paperUnitReference (G := G))
    (paperUnitReference_mem_candidateHulls_of_norm_le_one (G := G) (l := l) hq)

/-- Exact semantic gap if the norm condition forces the lambda-O hull to be the
unit reference O: O is the unit normalization, not the paper Theta hull, and
its normalized log is the trivial unit log. -/
structure PaperQParameterHullUnitReferenceSemanticGap : Type where
  image_norm_le_one : Prop
  hull_subset_unitReference : Prop
  hull_eq_unitReference : Prop
  unitReference_log_trivial : Prop
  paperQParameterHull_semantics : Prop

/-- Exact missing semantic comparison. -/
def PaperQParameterHullUnitReferenceSemanticGapRequired : Prop :=
  Nonempty PaperQParameterHullUnitReferenceSemanticGap



/-- The actual zero signed label. -/
noncomputable def paperZeroLabel : SignedLabel l.value :=
  ⟨0, by
    constructor
    · omega
    · omega⟩

/-- The image point at the zero signed label. -/
noncomputable def paperQParameterZeroImagePoint : Block (G := G) :=
  paperQParameterImagePoint (G := G) (l := l) (paperZeroLabel (l := l))

/-- The zero-label image point is the unit of the tensor block. -/
theorem paperQParameterZeroImagePoint_eq_one :
    paperQParameterZeroImagePoint (G := G) (l := l) = 1 := by
  unfold paperQParameterZeroImagePoint paperQParameterImagePoint paperZeroLabel
  simp only [gaussExponent_zero, Nat.zero_eq, pow_zero]
  exact arithmeticTupleTprod_one (fun v (_ : Unit) => G.place v) (fun _ => ())

/-- The zero-label candidate lambda is nonzero. -/
theorem paperQParameterZeroImagePoint_ne_zero :
    paperQParameterZeroImagePoint (G := G) (l := l) ≠ 0 := by
  rw [paperQParameterZeroImagePoint_eq_one]
  exact one_ne_zero

/-- The zero-label image point is an actual lambda-O candidate containing the
whole possible image, under the norm condition. -/
theorem paperZeroCandidate_image_subset
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    paperQParameterImageSet (G := G) (l := l) ⊆
      paperScaledRegion (G := G) (paperQParameterZeroImagePoint (G := G) (l := l)) := by
  rw [paperQParameterZeroImagePoint_eq_one, paperScaledRegion_one]
  exact paperQParameterImageSet_subset_unitReference_of_norm_le_one
    (G := G) (l := l) hq

/-- The zero-label candidate is in the actual candidate family. -/
theorem paperZeroCandidate_mem_candidateHulls
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    paperScaledRegion (G := G) (paperQParameterZeroImagePoint (G := G) (l := l)) ∈
      paperCandidateHulls (G := G) (l := l) :=
  ⟨paperQParameterZeroImagePoint (G := G) (l := l),
    paperQParameterZeroImagePoint_ne_zero (G := G) (l := l),
    rfl,
    paperZeroCandidate_image_subset (G := G) (l := l) hq⟩

/-- The lambda-O hull is contained in the zero-label candidate. -/
theorem paperQParameterHull_subset_zeroCandidate
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    paperQParameterHull (G := G) (l := l) ⊆
      paperScaledRegion (G := G) (paperQParameterZeroImagePoint (G := G) (l := l)) :=
  paperQParameterHull_subset_scaledRegion_of_candidate (G := G) (l := l)
    (paperQParameterZeroImagePoint (G := G) (l := l))
    (paperQParameterZeroImagePoint_ne_zero (G := G) (l := l))
    (paperZeroCandidate_image_subset (G := G) (l := l) hq)

/-- Strict equality gap for the zero-label candidate. -/
structure PaperQParameterZeroCandidateEqualityGap
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) : Type where
  candidate_subset_hull : Prop
  hull_subset_candidate : Prop
  hull_eq_candidate : Prop

/-- Exact missing equality object. -/
def PaperQParameterZeroCandidateEqualityGapRequired
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) : Prop :=
  Nonempty (PaperQParameterZeroCandidateEqualityGap (G := G) (l := l) hq)


/-- The possible Theta image set using only the paper's positive theta labels
j = 1, ..., l*.  The zero label is the q-pilot label, not a Theta image.  The
image value is qUnit^(j^2); no extra 2l-th root is used. -/
noncomputable def paperQParameterNonzeroImageSet : Set (Block (G := G)) :=
  {x | ∃ j : SignedLabel l.value,
    1 ≤ (gaussExponent j.1).toNat ∧
    x = paperQParameterImagePoint (G := G) (l := l) j}

/-- Under the unit norm condition, the nonzero-label image is still contained in
O.  Thus excluding the zero label alone does not make lambda = 1 cease to be a
candidate. -/
theorem paperQParameterNonzeroImageSet_subset_unitReference_of_norm_le_one
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    paperQParameterNonzeroImageSet (G := G) (l := l) ⊆
      paperUnitReference (G := G) := by
  rintro x ⟨j, hj, rfl⟩
  exact paperQParameterImagePoint_mem_unitReference_of_norm_le_one
    (G := G) (l := l) hq j

/-- Exact structural gap: excluding the zero label does not remove the lambda=1
candidate under the norm condition because every qUnit power is still integral. -/
structure PaperQParameterNonzeroLabelsStillUnitCandidateGap : Type where
  nonzero_image_subset_unitReference : Prop
  lambdaOneStillCandidate : Prop
  needNonIntegralImageForNontriviality : Prop

/-- Exact missing nontriviality condition. -/
def PaperQParameterNonzeroLabelsStillUnitCandidateGapRequired : Prop :=
  Nonempty PaperQParameterNonzeroLabelsStillUnitCandidateGap


/-- Paper-facing name for the positive-label Theta image set. -/
noncomputable abbrev paperNonzeroImageSet : Set (Block (G := G)) :=
  paperQParameterNonzeroImageSet (G := G) (l := l)


/-- Coefficient lemma for the inverse pi-units equivalence, avoiding
Units.map/piUnits coefficient reduction. -/
theorem piUnits_symm_coe_apply
    (f : (v : V) → (CommonPrimeCompletion (G.place v))ˣ) :
    ((MulEquiv.piUnits.symm f :
        (∀ v : V, CommonPrimeCompletion (G.place v))ˣ) :
      (∀ v : V, CommonPrimeCompletion (G.place v))) =
      fun v => (f v : CommonPrimeCompletion (G.place v)) := rfl

/-- The actual qUnit tensor unit; its coefficient is a nonzero tensor. -/
noncomputable def paperQUnitLambdaUnit : (Block (G := G))ˣ :=
  Units.map (arithmeticTuplePureTensorMulHom
      (fun v (_ : Unit) => G.place v) (fun _ => ()))
    (MulEquiv.piUnits.symm (fun v => G.qUnit v))

/-- The actual qUnit tensor candidate lambda. -/
noncomputable def paperQUnitLambda : Block (G := G) :=
  (paperQUnitLambdaUnit (G := G) : Block (G := G))

/-- The qUnit tensor lambda is nonzero. -/
theorem paperQUnitLambda_ne_zero : paperQUnitLambda (G := G) ≠ 0 :=
  Units.ne_zero (paperQUnitLambdaUnit (G := G))

/-- The qUnit tensor is the pure tensor of the local qUnits. -/
theorem paperQUnitLambda_eq_tprod :
    paperQUnitLambda (G := G) =
      arithmeticTupleTprod (fun v (_ : Unit) => G.place v) (fun _ => ())
        (fun v => (G.qUnit v : CommonPrimeCompletion (G.place v))) := by
  unfold paperQUnitLambda paperQUnitLambdaUnit
  rw [Units.coe_map, piUnits_symm_coe_apply, arithmeticTuplePureTensorMulHom_apply]

/-- The scaled qUnit image point with exponent (j^2 - 1). -/
noncomputable def paperQUnitScaledImagePoint
    (j : SignedLabel l.value)
    (hj : 1 ≤ (gaussExponent j.1).toNat) : Block (G := G) :=
  arithmeticTupleTprod (fun v (_ : Unit) => G.place v) (fun _ => ())
    (fun v => (((G.qUnit v : G.valueCarrier v) ^
      ((gaussExponent j.1).toNat - 1) : (G.valueCarrier v)) :
        CommonPrimeCompletion (G.place v)))

/-- Nonzero-label image factorization through the qUnit tensor lambda. -/
theorem paperQParameterImagePoint_eq_qUnitLambda_mul
    (j : SignedLabel l.value)
    (hj : 1 ≤ (gaussExponent j.val).toNat) :
    paperQParameterImagePoint (G := G) (l := l) j =
      paperQUnitLambda (G := G) *
        paperQUnitScaledImagePoint (G := G) (l := l) j hj := by
  classical
  let n : Nat := (gaussExponent j.val).toNat
  rw [paperQUnitLambda_eq_tprod]
  change arithmeticTupleTprod (fun v (_ : Unit) => G.place v) (fun _ => ())
      (fun v => (((G.qUnit v : G.valueCarrier v) ^ n :
        (G.valueCarrier v)) : CommonPrimeCompletion (G.place v))) = _
  calc
    arithmeticTupleTprod (fun v (_ : Unit) => G.place v) (fun _ => ())
        (fun v => (((G.qUnit v : G.valueCarrier v) ^ n :
          (G.valueCarrier v)) : CommonPrimeCompletion (G.place v)))
        = arithmeticTupleTprod (fun v (_ : Unit) => G.place v) (fun _ => ())
            (fun v => (((G.qUnit v : G.valueCarrier v) *
              ((G.qUnit v : G.valueCarrier v) ^ (n - 1) : (G.valueCarrier v)) :
                (G.valueCarrier v)) : CommonPrimeCompletion (G.place v))) := by
          congr 1
          funext v
          have hnj : 1 ≤ n := by simpa [n] using hj
          exact congrArg Units.val (by
            rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hnj])
    _ = paperQUnitLambda (G := G) *
          paperQUnitScaledImagePoint (G := G) (l := l) j hj := by
          rw [paperQUnitScaledImagePoint, paperQUnitLambda_eq_tprod]
          exact (arithmeticTupleTprod_mul
            (places := fun v (_ : Unit) => G.place v)
            (tuple := fun _ => ())
            (x := fun v => (G.qUnit v : CommonPrimeCompletion (G.place v)))
            (y := fun v => (((G.qUnit v : G.valueCarrier v) ^
              ((gaussExponent j.val).toNat - 1) : (G.valueCarrier v)) :
                CommonPrimeCompletion (G.place v)))).symm

/-- The scaled qUnit image point is integral under the unit norm condition. -/
theorem paperQUnitScaledImagePoint_mem_unitReference
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1)
    (j : SignedLabel l.value)
    (hj : 1 ≤ (gaussExponent j.1).toNat) :
    paperQUnitScaledImagePoint (G := G) (l := l) j hj ∈
      paperUnitReference (G := G) := by
  classical
  let n : Nat := (gaussExponent j.1).toNat
  let u : (v : V) → CommonPrimeCompletion (G.place v) :=
    fun v => (((G.qUnit v : G.valueCarrier v) ^ (n - 1) :
      (G.valueCarrier v)) : CommonPrimeCompletion (G.place v))
  have hu : ∀ v : V, ‖u v‖ ≤ 1 := by
    intro v
    dsimp only [u]
    change ‖((G.qUnit v : CommonPrimeCompletion (G.place v)) ^ (n - 1))‖ ≤ 1
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hq v)
  have hint : IsIntegral ℤ_[p]
      (arithmeticTupleTprod (fun v (_ : Unit) => G.place v)
        (fun _ => ()) u) :=
    isIntegral_arithmeticTupleTprod_of_norm_le_one
      (fun v (_ : Unit) => G.place v) (fun _ => ()) u hu
  rw [paperUnitReference, arithmeticTupleCanonicalUnitReference_eq_integralClosure]
  have hmem : arithmeticTupleTprod (fun v (_ : Unit) => G.place v)
      (fun _ => ()) u ∈
      (integralClosure ℤ_[p] (Block (G := G)) : Set (Block (G := G))) :=
    (mem_integralClosure_iff ℤ_[p] (Block (G := G))).mpr hint
  simpa only [u, n, paperQUnitScaledImagePoint] using hmem

/-- Nonzero-label image is contained in the qUnit tensor candidate region. -/
theorem paperQParameterNonzeroImageSet_subset_qUnitLambdaRegion
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    paperQParameterNonzeroImageSet (G := G) (l := l) ⊆
      paperScaledRegion (G := G) (paperQUnitLambda (G := G)) := by
  rintro x ⟨j, hj, rfl⟩
  refine ⟨paperQUnitScaledImagePoint (G := G) (l := l) j hj, ?_, ?_⟩
  · exact paperQUnitScaledImagePoint_mem_unitReference (G := G) (l := l) hq j hj
  · exact paperQParameterImagePoint_eq_qUnitLambda_mul (G := G) (l := l) j hj

/-- Actual qUnit tensor lambda-O candidate. -/
structure PaperQUnitLambdaCandidate
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) : Type where
  lam : Block (G := G)
  lam_eq : lam = paperQUnitLambda (G := G)
  lam_ne_zero : lam ≠ 0
  image_subset : paperQParameterNonzeroImageSet (G := G) (l := l) ⊆
    paperScaledRegion (G := G) lam

/-- The actual qUnit tensor candidate. -/
noncomputable def paperQUnitLambdaCandidate
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    PaperQUnitLambdaCandidate (G := G) (l := l) hq where
  lam := paperQUnitLambda (G := G)
  lam_eq := rfl
  lam_ne_zero := paperQUnitLambda_ne_zero (G := G)
  image_subset := paperQParameterNonzeroImageSet_subset_qUnitLambdaRegion
    (G := G) (l := l) hq

/-- The qUnit tensor candidate hull. -/
noncomputable def paperQUnitLambdaHull : Set (Block (G := G)) :=
  paperScaledRegion (G := G) (paperQUnitLambda (G := G))

/-- Exact equality gap between the nonzero-image qUnit candidate hull and the
full lambda-O hull (which also contains the zero-label image). -/
structure PaperQUnitHullEqualityGap : Type where
  nonzero_image_subset : Prop
  candidate_mem : Prop
  candidate_subset_hull : Prop
  hull_subset_candidate : Prop



/-- q-parameter unit lambda (single-underline q_v): alias of paperQUnitLambdaUnit.
This is a q-parameter object, not the double-underline root unit. -/
noncomputable abbrev qParameterUnitLambdaUnit : (Block (G := G))ˣ :=
  paperQUnitLambdaUnit (G := G)

/-- q-parameter unit lambda element. -/
noncomputable abbrev qParameterUnitLambda : Block (G := G) :=
  paperQUnitLambda (G := G)

/-- q-parameter scaled image point. -/
noncomputable abbrev qParameterUnitScaledImagePoint
    (j : SignedLabel l.value) (hj : 1 ≤ (gaussExponent j.1).toNat) :
    Block (G := G) :=
  paperQUnitScaledImagePoint (G := G) (l := l) j hj

/-- q-parameter unit lambda candidate. -/
noncomputable abbrev qParameterUnitLambdaCandidate
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    PaperQUnitLambdaCandidate (G := G) (l := l) hq :=
  paperQUnitLambdaCandidate (G := G) (l := l) hq

/-- q-parameter unit lambda-O hull. -/
noncomputable abbrev qParameterUnitLambdaHull : Set (Block (G := G)) :=
  paperQUnitLambdaHull (G := G)

/-- Alias of the q-parameter image inclusion in the qUnit-lambda region. -/
theorem paperQParameterNonzeroImageSet_subset_qParameterUnitLambdaRegion
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    paperQParameterNonzeroImageSet (G := G) (l := l) ⊆
      paperScaledRegion (G := G) (qParameterUnitLambda (G := G)) :=
  paperQParameterNonzeroImageSet_subset_qUnitLambdaRegion (G := G) (l := l) hq

end LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
end
