import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionPacketLogShell
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceLogShell
import LeanFormal.IUT.IUTIII.Theorem311.SourceLogShellFamilyDependent

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Landing actual integral-unit logarithms in the arithmetic tensor packet

This file assembles the codomain side of the source-unit logarithm: an actual
family of integral units at the finite places of every packet factor is sent
by `completionUnitLog` into the corresponding arithmetic log-shell tensor.
It proves the packet-region and tuple-region memberships and the compatibility
of the tuple projection.

Boundary: this is only codomain assembly from actual integral-unit packets to
the actual IQ tensor/log region.  It does not construct a theta-pilot source
image, does not define a Kummer map from `OriginalInput`, and does not claim
that N5 is closed.  The single-coordinate power laws below are proved
Kummer-transition fragments: they convert a root/power transition in one
actual unit coordinate into the corresponding scalar on the landed tensor.
-/

namespace LeanFormal.IUT

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule

noncomputable section

universe uK uI uV

/-- The actual unit logarithm at a common-prime place lies in the integral
log-shell attached to the corresponding normalized completion. -/
theorem completionUnitLog_mem_commonPrimeCompletion_integralLogShell
    {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    (place : FinitePlaceAtPrime K p)
    (u : (CompletionIntegers (K := K) place.val)ˣ) :
    completionUnitLog (K := K) place.val u ∈
      (integralLogShell (K := CommonPrimeCompletion place) (p := p) :
        Set (CommonPrimeCompletion place)) := by
  exact (commonPrimeCompletion_logShell_iff (p := p) place
    (completionUnitLog (K := K) place.val u)).mpr (by
      change completionUnitLog (K := K) place.val u ∈ completionLogShell place.val
      exact completionUnitLog_mem_logShell (K := K) place.val u)

/-- Land a family of actual integral-unit logarithms in the arithmetic packet
tensor.  Each packet coordinate receives the logarithm of the selected unit at
that place. -/
def arithmeticUnitPacketLogTensor
    {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type uI} [Fintype ι] {V : ι → Type uV} [∀ i, Fintype (V i)]
    (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (u : (i : ι) → (v : V i) →
      (CompletionIntegers (K := K) (places i v).val)ˣ) :
    ArithmeticPacketTensor places :=
  finitePadicTensorTprod (p := p) (fun i => CompletionPacket (places i))
    (fun i v => completionUnitLog (places i v).val (u i v))

/-- The packet-level unit logarithm is a member of the actual arithmetic tensor
log region. -/
theorem arithmeticUnitPacketLogTensor_mem_arithmeticTensorLogRegion
    {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type uI} [Fintype ι] {V : ι → Type uV} [∀ i, Fintype (V i)]
    (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (u : (i : ι) → (v : V i) →
      (CompletionIntegers (K := K) (places i v).val)ˣ) :
    arithmeticUnitPacketLogTensor (p := p) places u ∈
      arithmeticTensorLogRegion (p := p) places := by
  rw [arithmeticTensorLogRegion, tensorIntegralRegion]
  exact ⟨(fun i v => completionUnitLog (places i v).val (u i v)),
    (fun i _ v _ =>
      completionUnitLog_mem_commonPrimeCompletion_integralLogShell
        (p := p) (places i v) (u i v)),
    rfl⟩

/-- Land a tuple of actual integral-unit logarithms in the corresponding
arithmetic tensor block. -/
def arithmeticUnitTupleLogTensor
    {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type uI} [Fintype ι] {V : ι → Type uV}
    (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : ι) → V i)
    (u : (i : ι) →
      (CompletionIntegers (K := K) (places i (tuple i)).val)ˣ) :
    ArithmeticTensorTupleBlock places tuple :=
  finitePadicTensorTprod (p := p)
    (fun i => CommonPrimeCompletion (places i (tuple i)))
    (fun i => completionUnitLog (places i (tuple i)).val (u i))

/-- The tuple-level unit logarithm is a member of the actual tuple log region. -/
theorem arithmeticUnitTupleLogTensor_mem_arithmeticTensorTupleLogRegion
    {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type uI} [Fintype ι] {V : ι → Type uV}
    (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : ι) → V i)
    (u : (i : ι) →
      (CompletionIntegers (K := K) (places i (tuple i)).val)ˣ) :
    arithmeticUnitTupleLogTensor (p := p) places tuple u ∈
      arithmeticTensorTupleLogRegion (p := p) places tuple := by
  rw [arithmeticTensorTupleLogRegion, tensorLogShellRegion]
  exact ⟨(fun i => completionUnitLog (places i (tuple i)).val (u i)),
    (fun i _ =>
      completionUnitLog_mem_commonPrimeCompletion_integralLogShell
        (p := p) (places i (tuple i)) (u i)),
    rfl⟩

/-- The tuple projection sends the packet-level unit logarithm to the tuple
chosen by the projection. -/
theorem arithmeticTensorTupleProjection_arithmeticUnitPacketLogTensor
    {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type uI} [Fintype ι] {V : ι → Type uV} [∀ i, Fintype (V i)]
    (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : ι) → V i)
    (u : (i : ι) → (v : V i) →
      (CompletionIntegers (K := K) (places i v).val)ˣ) :
    arithmeticTensorTupleProjection (p := p) places tuple
        (arithmeticUnitPacketLogTensor (p := p) places u) =
      arithmeticUnitTupleLogTensor (p := p) places tuple
        (fun i => u i (tuple i)) := by
  simpa [arithmeticUnitPacketLogTensor, arithmeticUnitTupleLogTensor] using
    arithmeticTensorTupleProjection_tprod (p := p) places tuple
      (fun i v => completionUnitLog (places i v).val (u i v))

/-- Scaling one tensor coordinate of a pure p-adic tensor scales the whole
tensor by the same p-adic scalar. -/
theorem finitePadicTensorTprod_update_smul
    {p : Nat} [Fact p.Prime] {ι : Type uI} [DecidableEq ι]
    {M : ι → Type uV} [∀ i, NormedAddCommGroup (M i)]
    [∀ i, NormedSpace ℚ_[p] (M i)] [∀ i, FiniteDimensional ℚ_[p] (M i)]
    (x : (i : ι) → M i) (iTarget : ι) (c : ℚ_[p]) :
    finitePadicTensorTprod (p := p) M
        (Function.update x iTarget (c • x iTarget)) =
      c • finitePadicTensorTprod (p := p) M x := by
  simpa only [Function.update_eq_self] using
    (finitePadicTensorTprod (p := p) M).map_update_smul x iTarget c (x iTarget)

/-- Raising the unit at one packet coordinate to a natural power multiplies
the corresponding unit-log tensor by that natural scalar.  No other tensor
coordinate is changed. -/
theorem arithmeticUnitPacketLogTensor_update_pow
    {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type uI} [Fintype ι] [DecidableEq ι]
    {V : ι → Type uV} [∀ i, Fintype (V i)]
    (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (iTarget : ι) (n : Nat)
    (u : (i : ι) → (v : V i) →
      (CompletionIntegers (K := K) (places i v).val)ˣ) :
    arithmeticUnitPacketLogTensor (p := p) places
        (Function.update u iTarget (fun v => (u iTarget v) ^ n)) =
      n • arithmeticUnitPacketLogTensor (p := p) places u := by
  let x : (i : ι) → CompletionPacket (places i) :=
    fun i v => completionUnitLog (places i v).val (u i v)
  have hx : (fun i v => completionUnitLog (places i v).val
        ((Function.update u iTarget (fun v => (u iTarget v) ^ n)) i v)) =
      Function.update x iTarget ((n : ℚ_[p]) • x iTarget) := by
    funext i v
    by_cases hi : i = iTarget
    · subst i
      simp [x, Function.update_self, completionUnitLog_pow, Algebra.smul_def, map_natCast]
      rfl
    · simp [x, Function.update_of_ne hi]
  unfold arithmeticUnitPacketLogTensor
  rw [hx]
  rw [finitePadicTensorTprod_update_smul]
  rw [Nat.cast_smul_eq_nsmul]

/-- Tuple form of the single-coordinate power law: raising the unit at one
tuple coordinate to a natural power scales the tuple-log tensor by that
natural scalar, with every other coordinate fixed. -/
theorem arithmeticUnitTupleLogTensor_update_pow
    {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type uI} [Fintype ι] [DecidableEq ι] {V : ι → Type uV}
    (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : ι) → V i) (iTarget : ι) (n : Nat)
    (u : (i : ι) →
      (CompletionIntegers (K := K) (places i (tuple i)).val)ˣ) :
    arithmeticUnitTupleLogTensor (p := p) places tuple
        (Function.update u iTarget ((u iTarget) ^ n)) =
      n • arithmeticUnitTupleLogTensor (p := p) places tuple u := by
  let x : (i : ι) → CommonPrimeCompletion (places i (tuple i)) :=
    fun i => completionUnitLog (places i (tuple i)).val (u i)
  have hx : (fun i => completionUnitLog (places i (tuple i)).val
        ((Function.update u iTarget ((u iTarget) ^ n)) i)) =
      Function.update x iTarget ((n : ℚ_[p]) • x iTarget) := by
    funext i
    by_cases hi : i = iTarget
    · subst i
      simp [x, Function.update_self, completionUnitLog_pow, Algebra.smul_def, map_natCast]
      rfl
    · simp [x, Function.update_of_ne hi]
  unfold arithmeticUnitTupleLogTensor
  rw [hx]
  rw [finitePadicTensorTprod_update_smul]
  rw [Nat.cast_smul_eq_nsmul]

/-- Capsule-indexed dependent-family form of the packet-level unit logarithm. -/
abbrev arithmeticDependentUnitLogTensor
    {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {j : Nat} {Va : (i : Capsule j) → Type uV} [∀ i, Fintype (Va i)]
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p)
    (u : (i : Capsule j) → (v : Va i) →
      (CompletionIntegers (K := K) (places i v).val)ˣ) :
    arithmeticDependentTensorPacket (p := p) places :=
  arithmeticUnitPacketLogTensor (p := p) places u

/-- The dependent-family packet unit logarithm lies in the dependent tensor log
region (which is the existing arithmetic tensor log region definitionally). -/
theorem arithmeticDependentUnitLogTensor_mem_arithmeticDependentTensorLogRegion
    {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {j : Nat} {Va : (i : Capsule j) → Type uV} [∀ i, Fintype (Va i)]
    (places : (i : Capsule j) → Va i → FinitePlaceAtPrime K p)
    (u : (i : Capsule j) → (v : Va i) →
      (CompletionIntegers (K := K) (places i v).val)ˣ) :
    arithmeticDependentUnitLogTensor (p := p) places u ∈
      arithmeticDependentTensorLogRegion (p := p) places := by
  rw [arithmeticDependentTensorLogRegion_eq_arithmeticTensorLogRegion]
  exact arithmeticUnitPacketLogTensor_mem_arithmeticTensorLogRegion
    (p := p) places u

/-! ## Axiom probes -/

#print axioms completionUnitLog_mem_commonPrimeCompletion_integralLogShell
#print axioms arithmeticUnitPacketLogTensor
#print axioms arithmeticUnitPacketLogTensor_mem_arithmeticTensorLogRegion
#print axioms arithmeticUnitTupleLogTensor
#print axioms arithmeticUnitTupleLogTensor_mem_arithmeticTensorTupleLogRegion
#print axioms arithmeticTensorTupleProjection_arithmeticUnitPacketLogTensor
#print axioms finitePadicTensorTprod_update_smul
#print axioms arithmeticUnitPacketLogTensor_update_pow
#print axioms arithmeticUnitTupleLogTensor_update_pow
#print axioms arithmeticDependentUnitLogTensor
#print axioms arithmeticDependentUnitLogTensor_mem_arithmeticDependentTensorLogRegion

end

end LeanFormal.IUT
