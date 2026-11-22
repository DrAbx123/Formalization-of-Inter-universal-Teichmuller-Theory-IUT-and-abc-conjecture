import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionPacket
import LeanFormal.IUT.Foundations.LocalFields.FiniteProductRationalSpan
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorLogShellRegion

/-! The actual logarithmic integral region in the whole finite completion packet. -/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldIntegralUnits LeanFormal.IUT.LocalFieldLogarithm

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {V : Type*} [Fintype V]

def commonPrimeCompletionActualRingEquiv (place : FinitePlaceAtPrime K p) :
    CommonPrimeCompletion place ≃+* Completion place.val :=
  (commonPrimeCompletionRingEquiv place).trans (normalizedCompletionRingEquiv place.val)

theorem commonPrimeCompletion_logShell_iff (place : FinitePlaceAtPrime K p)
    (x : CommonPrimeCompletion place) :
    x ∈ integralLogShell (K := CommonPrimeCompletion place) (p := p) ↔
      commonPrimeCompletionActualRingEquiv place x ∈ completionLogShell place.val := by
  rcases place with ⟨place, hprime⟩
  cases hprime
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    have hyx : y = x := (normalizedCompletionRingEquiv place).injective hxy
    rw [← hyx]
    exact hy

def completionPacketLogRegion (places : V → FinitePlaceAtPrime K p) :
    Set (CompletionPacket places) :=
  Set.pi Set.univ (fun v =>
    (integralLogShell (K := CommonPrimeCompletion (places v)) (p := p) :
      Set (CommonPrimeCompletion (places v))))

theorem isCompact_completionPacketLogRegion (places : V → FinitePlaceAtPrime K p) :
    IsCompact (completionPacketLogRegion places) :=
  isCompact_univ_pi (fun v =>
    isCompact_integralLogShell (K := CommonPrimeCompletion (places v)) (p := p))

theorem zero_mem_completionPacketLogRegion (places : V → FinitePlaceAtPrime K p) :
    (0 : CompletionPacket places) ∈ completionPacketLogRegion places :=
  fun _ _ => AddSubgroup.zero_mem _

theorem one_mem_completionPacketLogRegion (places : V → FinitePlaceAtPrime K p) :
    (1 : CompletionPacket places) ∈ completionPacketLogRegion places :=
  fun v _ => integers_subset_integralLogShell (p := p)
    ((Integers (CommonPrimeCompletion (places v))).one_mem)

theorem rat_span_completionPacketLogRegion_eq_top (places : V → FinitePlaceAtPrime K p) :
    Submodule.span ℚ (completionPacketLogRegion places) = ⊤ := by
  exact FiniteProductRationalSpan.rat_span_pi_eq_top _
    (fun _ => AddSubgroup.zero_mem _)
    (fun v => LocalFieldPadicTensor.rat_span_integralLogShell_eq_top
      (fun v => CommonPrimeCompletion (places v)) v)

end

end LeanFormal.IUT.NumberFieldFinitePlace
