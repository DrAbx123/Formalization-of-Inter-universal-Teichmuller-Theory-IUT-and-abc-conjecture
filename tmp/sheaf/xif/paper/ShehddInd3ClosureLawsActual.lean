import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind3Reduction

/-!
# ShehddInd3ClosureLawsActual — (Ind3) upper-semi possible-image closure laws

STEP 0 prior-art (reuse only): IUT III Indeterminacy/Ind3Reduction.lean provides
* PossibleImage beta (carrier : Set beta) with the one-sided dominance preorder;
* lowerClosure (down-closure), lowerClosure_monotone / lowerClosure_idem,
  lowerClosure_isLowerClosed;
* IsLowerClosed and le_iff_carrier_subset_of_isLowerClosed.

This file adds the order-theoretic closure laws needed by the (Ind3) upper-semi
comparison consumers: a possible image is down-closed iff it is its own down-closure,
and the comparison against a down-closed image is set inclusion of closures.
No new assumptions, no sorry/axiom; the analytic (Ind3) source carriers remain NAMED
(see Ind3.lean:45 audit note and the open card logs/coordination/ind3-reduction-20261016.md).
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddInd3ClosureLawsActual

open LeanFormal.IUT
open LeanFormal.IUT.PossibleImage

variable {β : Type*} [Preorder β]

/-- **PROVED:** a possible image is down-closed exactly when it equals its own
downward closure. -/
theorem isLowerClosed_iff_lowerClosure_eq_self (φ : PossibleImage β) :
    IsLowerClosed φ ↔ lowerClosure φ = φ := by
  constructor
  · intro hcl
    apply PossibleImage.ext
    intro z
    constructor
    · intro hz
      rw [mem_lowerClosure] at hz
      obtain ⟨w, hw, hzw⟩ := hz
      exact hcl hw hzw
    · intro hz
      rw [mem_lowerClosure]
      exact ⟨z, hz, le_rfl⟩
  · intro heq z w hw hzw
    have hz : z ∈ lowerClosure φ := by
      rw [mem_lowerClosure]
      exact ⟨w, hw, hzw⟩
    rwa [heq] at hz

/-- **PROVED:** comparing a possible image with a down-closed one is the same as
comparing carriers (one-sided upper-semi reading of (CnfInd3)). -/
theorem lowerClosure_le_iff_carrier_subset {φ ψ : PossibleImage β}
    (hψ : IsLowerClosed ψ) :
    lowerClosure φ ≤ ψ ↔ (lowerClosure φ).carrier ⊆ ψ.carrier :=
  le_iff_carrier_subset_of_isLowerClosed (φ := lowerClosure φ) (ψ := ψ) hψ

/-- **PROVED:** the down-closure of a down-closed image is itself. -/
theorem lowerClosure_eq_self_of_isLowerClosed {φ : PossibleImage β}
    (h : IsLowerClosed φ) : lowerClosure φ = φ :=
  (isLowerClosed_iff_lowerClosure_eq_self φ).mp h

/-- Row record: reused (Ind3) reduction laws vs the added closure laws. -/
def ind3ClosureRows : List (String × String × String) :=
  [ ("down-closure monotone / idempotent / down-closed", "REUSED PROVED", "Ind3Reduction.lowerClosure_monotone / lowerClosure_idem / lowerClosure_isLowerClosed")
  , ("comparison vs down-closed image = carrier inclusion", "REUSED PROVED", "Ind3Reduction.le_iff_carrier_subset_of_isLowerClosed")
  , ("isLowerClosed <-> lowerClosure = self", "NEW PROVED", "isLowerClosed_iff_lowerClosure_eq_self")
  , ("closure comparison via carrier inclusion", "NEW PROVED", "lowerClosure_le_iff_carrier_subset")
  , ("analytic (Ind3) log-Kummer carriers", "NAMED", "Ind3.lean audit note; logs/coordination/ind3-reduction-20261016.md") ]

theorem ind3ClosureRows_length : ind3ClosureRows.length = 5 := rfl

#check isLowerClosed_iff_lowerClosure_eq_self
#check lowerClosure_le_iff_carrier_subset
#check lowerClosure_eq_self_of_isLowerClosed
#check ind3ClosureRows_length

end LeanFormal.IUT.XiFPaper.ShehddInd3ClosureLawsActual
end
