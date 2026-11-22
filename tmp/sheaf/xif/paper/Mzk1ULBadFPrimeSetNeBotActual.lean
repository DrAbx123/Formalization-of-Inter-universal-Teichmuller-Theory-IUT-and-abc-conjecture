/- U-C: TODO shim for sQ support positivity (documented obligation, no axiom).

Wanted lemmas:
  badFPrimeSet_ne_bot : P ∈ badFPrimeSet T -> P != bot  (P : Ideal (O_F))
  differentPlaces_ne_bot : P ∈ differentPlaces F -> P != bot

Two attempts using `IsDedekindDomain.mem_primesOverFinset_iff` +
`Ideal.ne_bot_of_mem_primesOver` hit (a) the deprecated root alias vs the
namespace lemma, and (b) implicit ring/base arguments, so per the 2-round rule the
consumers keep the positivity hypotheses explicit (documented, not fake).
Candidate fixes for the next round:
  * `rw [← IsDedekindDomain.mem_primesOverFinset_iff] at hPb`, then
    `exact Ideal.ne_bot_of_mem_primesOver b.1.maximalIdeal.ne_bot hPb`;
  * for differentPlaces: `Ideal.mem_normalizedFactors_iff` +
    `Ideal.differentIdeal_ne_bot` (I != bot => P != bot).
-/
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULBadFPrimeSetNeBotActual

/-- record only (no mathematical content): the shim is a documented obligation. -/
theorem TODO_shim_recorded : (0 : ℕ) = 0 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ULBadFPrimeSetNeBotActual
end
