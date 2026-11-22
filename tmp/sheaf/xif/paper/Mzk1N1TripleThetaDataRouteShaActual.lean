import Mathlib.Tactic

/-!
# A704 new route N1: triple-dependent Theta-data (Sha, audit only)

RETRACTION (A704): the old `final_conditional_ABC` / `natRadicalWeightBound_iff_ABC`
chain is RETRACTED as vacuous: its `hfull` hypothesis is unsatisfiable at fixed `T`
(machine proof `Mzk1FinalConditionalVacuityShaActual.hfull_unsatisfiable`).  The
`N = a+b+c+1` scaling is not the paper structure, and the 3.12 chain is not load-bearing.

New route N1 (all new work):
* triple-dependent `Theta`-data;
* bad primes = primes of `abc`;
* `q = (abc)^2` (so `v_p(q) = 2 v_p(abc)`);
* normalized weight `Sum_{p | abc} log p`, with the local normalization
  `Sum_{v | p} ([F_v : Q_p]/[F : Q]) * v_p(.) * log p = log p`.

This file is an audit/route record only; the N1 model itself is the abc lane's task.
No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1N1TripleThetaDataRouteShaActual

structure RouteRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def routeRows : List RouteRow :=
  [ ⟨"legacy final_conditional_ABC", "RETRACTED: hfull unsatisfiable (see vacuity Sha)", "RETRACTED"⟩
  , ⟨"natRadicalWeightBound_iff_ABC", "RETRACTED: vacuous via hfull", "RETRACTED"⟩
  , ⟨"N = a+b+c+1 scaling", "RETRACTED: not the paper structure", "RETRACTED"⟩
  , ⟨"N1 Theta-data", "triple-dependent; bad = primes(abc); q = (abc)^2", "NEW_ROUTE"⟩
  , ⟨"N1 normalized weight", "Sum_p log p; local [F_v:Q_p]/[F:Q] normalization", "NEW_ROUTE"⟩
  , ⟨"N1 model", "abc lane task (not proved here)", "PENDING_ABC_LANE"⟩
  , ⟨"scope", "route/audit only; no conclusion claimed", "INTEGRITY"⟩
  ]

theorem routeRows_length : routeRows.length = 7 := rfl

theorem routeRows_statuses_ok :
    routeRows.all (fun r =>
      r.status ∈ ["RETRACTED", "NEW_ROUTE", "PENDING_ABC_LANE", "INTEGRITY"]) = true := by
  decide

theorem route_has_only_n1_work :
    routeRows.any (fun r => r.status = "NEW_ROUTE") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1N1TripleThetaDataRouteShaActual
