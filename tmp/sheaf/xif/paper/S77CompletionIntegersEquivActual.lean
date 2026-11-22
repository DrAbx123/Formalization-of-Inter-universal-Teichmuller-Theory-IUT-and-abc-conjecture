import tmp.sheaf.xif.paper.S63OBoundaryLogShellActual

/-! # S77: conditional identity ring equivalence for the two integral rings

The two integral rings live on the same completion but with different norm
instances:

* CompletionIntegers place is the adic-completion integral ring;
* Integers (CommonPrimeCompletion place) is the unit ball of the normalized
  spectral norm on CommonPrimeCompletion.

FinitePlaceNormalizedCompletion explicitly states that integer-ring
compatibility is a separate theorem: a homeomorphism does not identify unit
balls.  Hence no unconditional identity RingEquiv can be built from the frozen
source.

This file gives the minimal actual transport API: a carrier-membership
hypothesis, and the actual identity RingEquiv built from it.  The hypothesis is
recorded as an exact requirement; no inhabitant is asserted.

No fake equivalence/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S77CompletionIntegersEquivActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

/-- Minimal actual carrier-transport hypothesis: the two integral rings have
the same elements in the common completion. -/
def completionIntegersCarrierEq : Prop :=
  ∀ x : CommonPrimeCompletion place,
    x ∈ CompletionIntegers place.val ↔
      x ∈ Integers (CommonPrimeCompletion place)

/-- From the actual carrier equality, the identity map is a ring equivalence. -/
noncomputable def completionIntegersRingEquivOfCarrierEq
    (h : completionIntegersCarrierEq (K := K) (p := p) place) :
    (CompletionIntegers place.val : Type u) ≃+*
      Integers (CommonPrimeCompletion place) where
  toFun := fun x =>
    ⟨x.1, (h x.1).mp x.2⟩
  invFun := fun y =>
    ⟨y.1, (h y.1).mpr y.2⟩
  left_inv := by
    intro x
    ext
    rfl
  right_inv := by
    intro y
    ext
    rfl
  map_add' := by
    intro x y
    ext
    rfl
  map_mul' := by
    intro x y
    ext
    rfl

/-- The exact missing carrier transport; no inhabitant asserted. -/
def completionIntegersCarrierEqRequired : Prop :=
  completionIntegersCarrierEq (K := K) (p := p) place

end LeanFormal.IUT.XiFPaper.S77CompletionIntegersEquivActual

end
