import tmp.sheaf.n8.closure.NativeSplitMultiplicativeAttempt

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Native reduction-rest assembly actual

Actual from existing native files:
- stable/multiplicative reduction at every bad lift (clauses A/B);
- real qParameter with nonzero, contracting, q != 1, and stable-reduction
  compatibility, from the native Tate witness (Wave30 qParameter).

Exact gap: the split-multiplicative reduction card.  Given that card, the
whole NativeReductionRestRemaining is assembled actually and the full
NativeReductionRest follows.  No arbitrary reduction data is used.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt
open LeanFormal.IUT.N8Closure.NativeBadFintypeSourceAttempt
open LeanFormal.IUT.N8Closure.NativeBadFiniteTargetCorrection
open LeanFormal.IUT.N8Closure.NativeContractFromBadFinite
open LeanFormal.IUT.N8Closure.NativeReductionRestActual
open LeanFormal.IUT.N8Closure.NativeQParameterActual
open LeanFormal.IUT.N8Closure.NativeSplitMultiplicativeAttempt
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.N8Closure.EtaReductionRestAssemblyActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual qParameter package from the native Tate witnesses. -/
noncomputable def qParameterActual : NativeQParameterData X :=
  nativeQParameterData X

theorem qParameterActual_fields :
    (∀ b : NativeBadPlaces X, (qParameterActual (X := X)).qParameter b ≠ 0) ∧
      (∀ b : NativeBadPlaces X, ‖(qParameterActual (X := X)).qParameter b‖ < 1) ∧
      (∀ b : NativeBadPlaces X, (qParameterActual (X := X)).qParameter b ≠ 1) :=
  ⟨(qParameterActual (X := X)).qParameter_nonzero,
   (qParameterActual (X := X)).qParameter_contracting,
   (qParameterActual (X := X)).qParameter_ne_one⟩

/-- Assembly input: the single exact missing split-multiplicative card. -/
abbrev ReductionRestAssemblyInput (X : N8NativeInput l) : Prop :=
  NativeSplitMultiplicativeCard X

/-- Actual assembly of NativeReductionRestRemaining from the single split card;
all other fields are actual qParameter data. -/
noncomputable def reductionRestRemainingOfAssembly
    (C : ReductionRestAssemblyInput X) :
    NativeReductionRestRemaining X :=
  nativeReductionRestRemainingOfSplit X C

/-- Actual full NativeReductionRest from the split card. -/
noncomputable def reductionRestOfAssembly
    (C : ReductionRestAssemblyInput (X := X)) :
    NativeReductionRest X :=
  nativeReductionRestOfRemaining X
    (reductionRestRemainingOfAssembly (X := X) C)

/-- Exact characterization: a reduction-rest remaining exists iff the split
card/target is supplied. -/
theorem reductionRestRemaining_nonempty_iff_split :
    Nonempty (NativeReductionRestRemaining X) ↔
      NativeSplitMultiplicativeTarget X := by
  constructor
  · rintro ⟨R⟩
    exact R.splitMultiplicativeReduction
  · intro h
    exact ⟨nativeReductionRestRemainingOfSplit X ⟨h⟩⟩

/-- Exact gap: the split-multiplicative target is not derived from the current
native data. -/
def ReductionRestAssemblyGap : Prop :=
  ¬ NativeSplitMultiplicativeTarget X

end LeanFormal.IUT.N8Closure.EtaReductionRestAssemblyActual

end