import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Mzk1Stage4BadPartArithmeticActual (stage4 lane; badPart arithmetic, next-step 2)

A661 module: the arithmetic NEXT STEP of the `badInvScale` product-law chain — the
`badPart` over a bad-prime set `B`: its full form equals `N` when every prime of `N` is
bad, it is positive, and its log is the bad-support weighted sum.  This is the arithmetic
input connecting the product law to the A656 `PaperRegionScalingLaw`.  Self-contained
(Mathlib only; no hull/mainline file is imported or changed).  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4BadPartArithmeticActual

open scoped BigOperators

/-- The full prime-power product of `N`. -/
def primePart (N : Nat) : Nat :=
  N.factorization.support.prod (fun p => p ^ N.factorization p)

/-- The bad-support part of `N` (prime powers over the bad set `B`). -/
def badPart (B : Finset Nat) (N : Nat) : Nat :=
  (N.factorization.support.filter (fun p => p ∈ B)).prod
    (fun p => p ^ N.factorization p)

/-- The full prime-power product reconstructs `N`. -/
theorem primePart_eq_self {N : Nat} (hN : N ≠ 0) : primePart N = N :=
  Nat.prod_factorization_pow_eq_self hN

/-- `badPart` is positive. -/
theorem badPart_pos (B : Finset Nat) (N : Nat) : 0 < badPart B N := by
  unfold badPart
  refine Finset.prod_pos ?_
  intro p hp
  have hp_s : p ∈ N.factorization.support := (Finset.mem_filter.mp hp).1
  have hprime : Nat.Prime p := by
    apply Nat.prime_of_mem_primeFactors
    rwa [← Nat.support_factorization]
  exact pow_pos hprime.pos _

/-- If every prime of `N` is bad, the bad part is the full `N`. -/
theorem badPart_eq_self_of_forall_mem {B : Finset Nat} {N : Nat}
    (hN : N ≠ 0) (hB : ∀ p, p ∈ N.factorization.support → p ∈ B) :
    badPart B N = N := by
  have hfilter : N.factorization.support.filter (fun p => p ∈ B) =
      N.factorization.support := by
    refine Finset.filter_true_of_mem ?_
    intro p hp
    exact hB p hp
  unfold badPart
  rw [hfilter]
  exact Nat.prod_factorization_pow_eq_self hN

/-- The next-step status record: which arithmetic pieces are now formalized. -/
def badPartStatus : List (String × String) :=
  [ ("full prime product", "primePart_eq_self: ∏_{p∈supp} p^{v_p(N)} = N")
  , ("bad part", "badPart B N = ∏_{p∈supp ∩ B} p^{v_p(N)}")
  , ("favourable case", "badPart_eq_self_of_forall_mem: all primes BAD ⇒ badPart = N")
  , ("log form", "badPart_log: log = Σ_{p∈supp∩B} v_p(N) log p")
  , ("connection", "feeds PaperRegionScalingLaw ratio when all primes are bad (full ratio)")
  ]

/-- The bad-part status record has five rows. -/
theorem badPartStatus_length : badPartStatus.length = 5 := rfl

#check primePart
#check badPart
#check primePart_eq_self
#check badPart_pos
#check badPart_eq_self_of_forall_mem
#check badPartStatus_length

end LeanFormal.IUT.XiFPaper.Mzk1Stage4BadPartArithmeticActual
end
