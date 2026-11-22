import tmp.sheaf.xif.paper.S423NatDivisorialAddMonoidActual
import tmp.sheaf.xif.paper.S432SmallModelActual

/-! # S506: ramification/q_v Phi model — exact universe boundary

The intended Phi has `obj X := ℕ` (S423) and pullback `n ↦ e(f) n`.  S423's
natDivisorialAddMonoid has carrier `ℕ : Type 0`, while S432's small base is
`Type (u+1)` and `DivisorialMonoidOn` requires object and carrier universes to
agree.  A universe-(u+1) divisorial monoid on `ULift ℕ` (with transported
integral/sharp/saturated proofs) is therefore required; it is not present.
`DvRamificationIndexData` and the `N·qOrder` submonoid are actual; the Phi
instance itself is exact missing.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S506QvPhiRamificationActual

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S423NatDivisorialAddMonoidActual
open LeanFormal.IUT.XiFPaper.S432SmallModelActual

universe u
variable (K : Type u) [Field K]

/-- Explicit ramification index data. -/
structure DvRamificationIndexData where
  e : ∀ {X Y : Example32SmallBase K}, (X ⟶ Y) → ℕ+
  e_id : ∀ X : Example32SmallBase K, e (𝟙 X) = 1
  e_comp : ∀ {X Y Z : Example32SmallBase K} (f : X ⟶ Y) (g : Y ⟶ Z),
    e (f ≫ g) = e f * e g
  e_iso : ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y), IsIso f → e f = 1

/-- Exact missing universe-lifted nat divisorial monoid: carrier `ULift ℕ`
at Type (u+1), with S423 integral/sharp/saturated transported. -/
structure DvNatDivisorialMonoidAtU where
  exists_monoid : Prop
  carrier_eq : Prop
  integral_sharp_saturated : Prop

/-- Exact missing ramification pullback Phi instance. -/
structure QvPhiRamificationModel where
  ramification : DvRamificationIndexData K
  phi : Prop
  pullback_mul_ramification : Prop
  characteristic_injective : Prop
  fsm_iso_e_one : Prop

def QvPhiRamificationModelRequired : Prop :=
  Nonempty (QvPhiRamificationModel K)

/-- The `N · qOrder` submonoid of `ℕ`. -/
def qvSectionSubmonoid (qOrder : ℕ) : AddSubmonoid ℕ where
  carrier := {n | ∃ k : ℕ, n = k * qOrder}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨m, rfl⟩ ⟨n, rfl⟩
    exact ⟨m + n, by ring⟩

end LeanFormal.IUT.XiFPaper.S506QvPhiRamificationActual
end
