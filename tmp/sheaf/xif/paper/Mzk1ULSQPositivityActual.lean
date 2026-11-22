/- U-C: sQ support positivity - DOCUMENTED TODO (no axiom, no consumer).

Wanted: P in badFPrimeSet T -> P != bot; P in differentPlaces F -> P != bot.
Attempts (two rounds, per the 2-round rule):
- root alias vs namespace: `mem_primesOverFinset_iff` deprecated in favour of
  `IsDedekindDomain.mem_primesOverFinset_iff` (DedekindDomain/Ideal/Lemmas:1179);
- rewriting `← IsDedekindDomain.mem_primesOverFinset_iff` in the goal leaves an
  unexpected base-ideal-nonzero goal (implicit-argument elaboration under
  autoImplicit), so the shim is parked as an obligation.
Candidate next step: prove directly from LiesOver: P in primesOverFinset p B gives
P.LiesOver p, hence if P = bot then comap P = bot contradicts p != bot
(`Ideal.comap_bot`/`Ideal.LiesOver`), avoiding the primesOver membership transfer.
`hq`/`hd` remain explicit in `Mzk1ULSQPaperActual.log_sQPaper_eq_sum_log` and its
re-export `Mzk1ULSQPaperUncondActual.log_sQPaper_eq_sum_log_uncond`.
-/
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULSQPositivityActual

/-- record only: the support positivity shims are documented obligations. -/
theorem TODO_positivity_recorded : (0 : ℕ) = 0 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ULSQPositivityActual
end
