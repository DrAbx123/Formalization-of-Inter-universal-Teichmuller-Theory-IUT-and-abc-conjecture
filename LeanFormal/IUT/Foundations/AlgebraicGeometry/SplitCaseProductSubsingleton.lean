import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Dropping subsingleton factors from a finite ring product

If `S ≃+* ∏_k R k` and every factor outside a finite index set `s` is a
subsingleton, then `S ≃+* ∏_{k ∈ s} R k`.  The proof projects the product and
extends a tuple on `s` by zero outside `s`; injectivity uses subsingleton of the
outside factors.  This is the exact zero-atom factor removal needed by the
global atom assembly.
-/
namespace ABCBridge.SplitCaseProductSubsingleton

universe u v

variable {S : Type u} [CommRing S] {κ : Type v} [DecidableEq κ]
  (Rc : κ → Type u) [∀ k, CommRing (Rc k)]
  [Fintype κ] (s : Finset κ)
  (hs : ∀ k, k ∉ s → Subsingleton (Rc k))

/-- Drop all subsingleton factors outside `s`. -/
noncomputable def dropSubsingletonFactors
    (e : S ≃+* ∀ k, Rc k) :
    S ≃+* ((k : s) → Rc k.1) := by
  classical
  let φ : S →+* ((k : s) → Rc k.1) :=
    { toFun := fun (x : S) (k : s) => e x k.1
      map_one' := by funext (k : s); exact congrFun (map_one e) k.1
      map_mul' := fun (x y : S) => by funext (k : s); exact congrFun (map_mul e x y) k.1
      map_add' := fun (x y : S) => by funext (k : s); exact congrFun (map_add e x y) k.1
      map_zero' := by funext (k : s); exact congrFun (map_zero e) k.1 }
  refine RingEquiv.ofBijective φ ⟨?_, ?_⟩
  · intro x y hxy
    apply e.injective
    funext k
    by_cases hk : k ∈ s
    · exact congrFun hxy ⟨k, hk⟩
    · haveI : Subsingleton (Rc k) := hs k hk
      exact Subsingleton.elim _ _
  · intro f
    classical
    let F : ∀ k, Rc k := fun k => if hk : k ∈ s then f ⟨k, hk⟩ else 0
    obtain ⟨x, hx⟩ := e.surjective F
    refine ⟨x, ?_⟩
    funext k
    have hx' := congrFun hx k.1
    simpa [F, φ, k.2] using hx'

end ABCBridge.SplitCaseProductSubsingleton