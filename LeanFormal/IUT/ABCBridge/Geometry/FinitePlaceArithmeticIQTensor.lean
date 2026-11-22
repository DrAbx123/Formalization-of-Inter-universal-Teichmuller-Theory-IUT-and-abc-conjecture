import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionPacketLogShell
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorIntegralRegion
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicEtaleTensorDecomposition

/-!
# The rational span of the actual arithmetic log-shell tensor region

Each factor keeps its whole finite packet of actual completions over the
same rational prime. IQ is defined as the rational span of their logarithmic
integral region in the genuine topological rational tensor. Its equality
with that tensor is proved for a nonempty factor family.

This is the local arithmetic carrier. No Gaussian region, procession,
degree weight, or log-volume estimate is supplied by this identification.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldPadicTensor

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)

abbrev ArithmeticPacketTensor :=
  FinitePadicTensor (p := p) (fun i => CompletionPacket (places i))

def arithmeticTensorLogRegion : Set (ArithmeticPacketTensor places) :=
  tensorIntegralRegion (p := p) (fun i => CompletionPacket (places i))
    (fun i => completionPacketLogRegion (places i))

def arithmeticIQCarrier : Submodule ℚ (ArithmeticPacketTensor places) :=
  Submodule.span ℚ (arithmeticTensorLogRegion places)

theorem isCompact_arithmeticTensorLogRegion :
    IsCompact (arithmeticTensorLogRegion places) :=
  isCompact_tensorIntegralRegion _ _ (fun i => isCompact_completionPacketLogRegion (places i))

omit [Fintype ι] in
theorem one_mem_arithmeticTensorLogRegion :
    (1 : ArithmeticPacketTensor places) ∈ arithmeticTensorLogRegion places := by
  refine ⟨fun _ => 1, ?_, rfl⟩
  exact fun i _ => one_mem_completionPacketLogRegion (places i)

omit [Fintype ι] in
theorem arithmeticIQCarrier_eq_top [Finite ι] [Nonempty ι] : arithmeticIQCarrier places = ⊤ :=
  rat_span_tensorIntegralRegion_eq_top _ _
    (fun i => rat_span_completionPacketLogRegion_eq_top (places i))

def arithmeticIQEquiv [Nonempty ι] :
    arithmeticIQCarrier places ≃ₗ[ℚ] ArithmeticPacketTensor places :=
  LinearEquiv.ofBijective (arithmeticIQCarrier places).subtype
    ⟨Subtype.val_injective, fun x => ⟨⟨x, by rw [arithmeticIQCarrier_eq_top]; trivial⟩, rfl⟩⟩

theorem arithmeticIQEquiv_apply [Nonempty ι] (x : arithmeticIQCarrier places) :
    arithmeticIQEquiv places x = x.val := rfl

def arithmeticIQHomeomorph [Nonempty ι] :
    arithmeticIQCarrier places ≃ₜ ArithmeticPacketTensor places :=
  (Homeomorph.setCongr (show (arithmeticIQCarrier places : Set (ArithmeticPacketTensor places)) =
      Set.univ from congrArg (fun P : Submodule ℚ (ArithmeticPacketTensor places) =>
        (P : Set (ArithmeticPacketTensor places))) (arithmeticIQCarrier_eq_top places))).trans
    (Homeomorph.Set.univ (ArithmeticPacketTensor places))

theorem arithmeticIQHomeomorph_apply [Nonempty ι] (x : arithmeticIQCarrier places) :
    arithmeticIQHomeomorph places x = x.val := rfl

theorem exists_arithmeticPacketTensor_fieldProduct :
    ∃ (J : Type (max u (max v w))) (_ : Fintype J) (E : J → Type (max u (max v w)))
      (_ : ∀ j, NontriviallyNormedField (E j)) (_ : ∀ j, NormedAlgebra ℚ_[p] (E j))
      (e : ArithmeticPacketTensor places ≃ₐ[ℚ_[p]] ((j : J) → E j)),
      (∀ j, FiniteDimensional ℚ_[p] (E j) ∧ CompleteSpace (E j) ∧ IsUltrametricDist (E j)) ∧
        Continuous e ∧ Continuous e.symm :=
  exists_finiteNormedFieldProduct_etaleTensor (fun i => CompletionPacket (places i))

end

end LeanFormal.IUT.NumberFieldFinitePlace
