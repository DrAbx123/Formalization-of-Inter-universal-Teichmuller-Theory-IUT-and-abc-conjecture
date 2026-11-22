import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceRelativeNormalizedCompletion
import LeanFormal.IUT.ABCBridge.Geometry.RelativeCompletionFinrankReduction
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import LeanFormal.IUT.Foundations.LocalFields.PadicFieldTowerDimension

/-!
# Actual local relative degrees and the tensor-block weights

The relative rank of the normalized fields is the already proved local e*f.
The actual Qp scalar tower gives absolute-rank multiplication, and finite
basis tensor ranks give the precise product of relative degrees in each
place-tuple block. The weights are computed from actual completion data.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldPadicTensor

noncomputable section

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem finrank_relativeNormalizedCompletion (place : FinitePlaceAtPrime K p) :
    Module.finrank (CommonPrimeCompletion (relativeCommonPrimePlace (k := k) place))
      (CommonPrimeCompletion place) = relativeCompletionDegree (k := k) place.val :=
  finrank_adicCompletion_eq_relativeCompletionDegree_unconditional place.val

theorem finrank_commonPrimeCompletion_moduleTower (place : FinitePlaceAtPrime K p) :
    Module.finrank ℚ_[p] (CommonPrimeCompletion (relativeCommonPrimePlace (k := k) place)) *
      Module.finrank (CommonPrimeCompletion (relativeCommonPrimePlace (k := k) place))
        (CommonPrimeCompletion place) = Module.finrank ℚ_[p] (CommonPrimeCompletion place) := by
  exact @finrank_padicFieldTower p _
    (CommonPrimeCompletion (relativeCommonPrimePlace (k := k) place))
    (CommonPrimeCompletion place) _ _ _ _ _
    (relativeNormalizedCompletionModuleTower (k := k) place)
    (commonPrimeCompletion_strongRankCondition _)
    (commonPrimeCompletion_moduleFree _)
    (relativeNormalizedCompletion_moduleFree place)

theorem finrank_commonPrimeCompletion_tower (place : FinitePlaceAtPrime K p) :
    Module.finrank ℚ_[p] (CommonPrimeCompletion (relativeCommonPrimePlace (k := k) place)) *
      relativeCompletionDegree (k := k) place.val =
      Module.finrank ℚ_[p] (CommonPrimeCompletion place) := by
  exact (congrArg
    (fun n => Module.finrank ℚ_[p]
      (CommonPrimeCompletion (relativeCommonPrimePlace (k := k) place)) * n)
    (finrank_relativeNormalizedCompletion (k := k) place).symm).trans
      (finrank_commonPrimeCompletion_moduleTower (k := k) place)

omit [Fact p.Prime] in
theorem relativeCommonPrimeCompletionDegree_pos (place : FinitePlaceAtPrime K p) :
    0 < relativeCompletionDegree (k := k) place.val := by
  rw [← finrank_relativeNormalizedCompletion]
  exact Module.finrank_pos

variable {ι : Type*} [Fintype ι]

def relativeCompletionTensorDegree (places : ι → FinitePlaceAtPrime K p) : ℕ :=
  ∏ i, relativeCompletionDegree (k := k) (places i).val

omit [Fact p.Prime] in
theorem relativeCompletionTensorDegree_pos (places : ι → FinitePlaceAtPrime K p) :
    0 < relativeCompletionTensorDegree (k := k) places :=
  Finset.prod_pos (fun i _ => relativeCommonPrimeCompletionDegree_pos (k := k) (places i))

theorem finrank_relativeCompletionTensor (places : ι → FinitePlaceAtPrime K p) :
    Module.finrank ℚ_[p] (FinitePadicTensor (p := p) (fun i => CommonPrimeCompletion (places i))) =
      relativeCompletionTensorDegree (k := k) places *
        Module.finrank ℚ_[p] (FinitePadicTensor (p := p)
          (fun i => CommonPrimeCompletion (relativeCommonPrimePlace (k := k) (places i)))) := by
  rw [finrank_finitePadicTensor, finrank_finitePadicTensor]
  unfold relativeCompletionTensorDegree
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [Nat.mul_comm] using (finrank_commonPrimeCompletion_tower (k := k) (places i)).symm

variable {V : ι → Type*}

def relativeCompletionTupleDegree (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : ι) → V i) : ℕ :=
  relativeCompletionTensorDegree (k := k) (fun i => places i (tuple i))

omit [Fact p.Prime] in
theorem relativeCompletionTupleDegree_pos (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : ι) → V i) : 0 < relativeCompletionTupleDegree (k := k) places tuple :=
  relativeCompletionTensorDegree_pos (k := k) _

instance relativeCompletionTupleDegreeNeZero
    (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i) :
    NeZero (relativeCompletionTupleDegree (k := k) places tuple) :=
  ⟨(relativeCompletionTupleDegree_pos places tuple).ne'⟩

abbrev RelativeCompletionTupleLabels (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : ι) → V i) := Fin (relativeCompletionTupleDegree (k := k) places tuple)

omit [Fact p.Prime] in
theorem card_relativeCompletionTupleLabels
    (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i) :
    Fintype.card (RelativeCompletionTupleLabels (k := k) places tuple) =
      relativeCompletionTupleDegree (k := k) places tuple := Fintype.card_fin _

theorem finrank_arithmeticTensorTupleBlock_relative
    (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i) :
    Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) =
      relativeCompletionTupleDegree (k := k) places tuple *
        Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock
          (fun i v => relativeCommonPrimePlace (k := k) (places i v)) tuple) :=
  finrank_relativeCompletionTensor (k := k) _

end

end LeanFormal.IUT.NumberFieldFinitePlace
