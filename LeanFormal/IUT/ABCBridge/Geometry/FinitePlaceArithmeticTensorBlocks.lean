import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticIQTensor
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorProductDistribution
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorNontrivial

/-!
# Actual completion tensor blocks indexed by place tuples

Distribute the actual finite completion packets without forgetting which
tuple of places labels each block. Every block projection maps the original
pure log-shell tensor region onto that tuple's actual log-shell tensor region.
This supplies the block labels required by the relative-degree weights.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldPadicTensor LeanFormal.IUT.LocalFieldLogarithm

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)

abbrev ArithmeticTensorTupleBlock (tuple : (i : ι) → V i) :=
  FinitePadicTensor (p := p) (fun i => CommonPrimeCompletion (places i (tuple i)))

def arithmeticTensorBlocksAlgEquiv :
    ArithmeticPacketTensor places ≃ₐ[ℚ_[p]]
      ((tuple : (i : ι) → V i) → ArithmeticTensorTupleBlock places tuple) :=
  finitePadicTensorProductAlgEquiv (fun i v => CommonPrimeCompletion (places i v))

open Classical in
def arithmeticTensorBlocksContinuousLinearEquiv :
    ArithmeticPacketTensor places ≃L[ℚ_[p]]
      ((tuple : (i : ι) → V i) → ArithmeticTensorTupleBlock places tuple) :=
  (arithmeticTensorBlocksAlgEquiv places).toLinearEquiv.toContinuousLinearEquiv

theorem arithmeticTensorBlocksAlgEquiv_tprod
    (x : (i : ι) → CompletionPacket (places i)) (tuple : (i : ι) → V i) :
    arithmeticTensorBlocksAlgEquiv places (finitePadicTensorTprod _ x) tuple =
      finitePadicTensorTprod (p := p) _ (fun i => x i (tuple i)) :=
  finitePadicTensorProductAlgEquiv_tprod _ x tuple

def arithmeticTensorTupleProjection (tuple : (i : ι) → V i) :
    ArithmeticPacketTensor places →ₗ[ℚ_[p]] ArithmeticTensorTupleBlock places tuple :=
  (LinearMap.proj tuple).comp (arithmeticTensorBlocksAlgEquiv places).toLinearMap

theorem arithmeticTensorTupleProjection_tprod
    (tuple : (i : ι) → V i) (x : (i : ι) → CompletionPacket (places i)) :
    arithmeticTensorTupleProjection places tuple (finitePadicTensorTprod _ x) =
      finitePadicTensorTprod (p := p) _ (fun i => x i (tuple i)) :=
  arithmeticTensorBlocksAlgEquiv_tprod places x tuple

theorem continuous_arithmeticTensorTupleProjection (tuple : (i : ι) → V i) :
    Continuous (arithmeticTensorTupleProjection places tuple) :=
  (arithmeticTensorTupleProjection places tuple).continuous_of_finiteDimensional

def arithmeticTensorTupleLogRegion (tuple : (i : ι) → V i) :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  tensorLogShellRegion (fun i => CommonPrimeCompletion (places i (tuple i)))

omit [∀ i, Fintype (V i)] in
theorem isCompact_arithmeticTensorTupleLogRegion (tuple : (i : ι) → V i) :
    IsCompact (arithmeticTensorTupleLogRegion places tuple) :=
  isCompact_tensorLogShellRegion _

omit [Fintype ι] [∀ i, Fintype (V i)] in
theorem one_mem_arithmeticTensorTupleLogRegion (tuple : (i : ι) → V i) :
    (1 : ArithmeticTensorTupleBlock places tuple) ∈ arithmeticTensorTupleLogRegion places tuple :=
  one_mem_tensorLogShellRegion _

theorem arithmeticTensorTupleProjection_image_logRegion (tuple : (i : ι) → V i) :
    arithmeticTensorTupleProjection places tuple '' arithmeticTensorLogRegion places =
      arithmeticTensorTupleLogRegion places tuple := by
  classical
  apply Set.Subset.antisymm
  · rintro z ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨fun i => x i (tuple i), ?_, ?_⟩
    · exact fun i _ => hx i (Set.mem_univ _) (tuple i) (Set.mem_univ _)
    · exact (arithmeticTensorTupleProjection_tprod places tuple x).symm
  · rintro z ⟨x, hx, rfl⟩
    let packet : (i : ι) → CompletionPacket (places i) := fun i => Pi.single (tuple i) (x i)
    refine ⟨finitePadicTensorTprod _ packet, ⟨packet, ?_, rfl⟩, ?_⟩
    · intro i _ v _
      by_cases hv : v = tuple i
      · subst v
        simpa only [packet, Pi.single_eq_same] using hx i (Set.mem_univ _)
      · dsimp only [packet]
        rw [Pi.single_eq_of_ne hv]
        exact AddSubgroup.zero_mem _
    · rw [arithmeticTensorTupleProjection_tprod]
      simp only [packet, Pi.single_eq_same]

omit [∀ i, Fintype (V i)] in
theorem finrank_arithmeticTensorTupleBlock (tuple : (i : ι) → V i) :
    Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) =
      ∏ i, Module.finrank ℚ_[p] (CommonPrimeCompletion (places i (tuple i))) :=
  finrank_finitePadicTensor _

omit [Fintype ι] [∀ i, Fintype (V i)] in
theorem finrank_arithmeticTensorTupleBlock_pos [Finite ι] (tuple : (i : ι) → V i) :
    0 < Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) := by
  letI := Fintype.ofFinite ι
  rw [finrank_arithmeticTensorTupleBlock]
  exact Finset.prod_pos (fun _ _ => Module.finrank_pos)

open Classical in
theorem finrank_arithmeticPacketTensor_eq_sum_blocks :
    Module.finrank ℚ_[p] (ArithmeticPacketTensor places) =
      ∑ tuple : (i : ι) → V i, Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) :=
  (arithmeticTensorBlocksAlgEquiv places).toLinearEquiv.finrank_eq.trans
    (Module.finrank_pi_fintype ℚ_[p])

end

end LeanFormal.IUT.NumberFieldFinitePlace
