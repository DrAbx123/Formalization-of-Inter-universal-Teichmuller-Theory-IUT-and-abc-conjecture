import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

open Polynomial

/-!
# STEP 0 prior-art: beta-avoiding parametric reduction -> qpilot audit: TauCeti has NO beta-avoiding Belyi variant; available Belyi assets only give q(S) subset {0,1} and CV subset {0,1}.  This file records the PRECISE reduction statement (blocker schema) and the exact obstruction; no fake.

# Mzk1BetaAvoidingReductionActual — parametric beta-tracking degree reduction (BLOCKER SCHEMA)

Target (Lead A329/A330): finite S with 2<|S|, beta notin S; construct f in Q[X]
with 0<deg f, CritIn01 f, |f(S)|<|S|, {0,1} subset f(S), f(beta) notin {0,1},
f(beta) notin f(S).
EXACT BLOCKER (honest): the TauCeti construction maps a=min S -> 0, b=max S -> 1,
c -> r; f = B_{m,n} o A; f(beta) = B_{m,n}(u) with u = A(beta) fixed rational.
f(S) subset {0,1}, so f(beta) notin f(S) reduces to f(beta) notin {0,1}.
f(beta)=0 iff u in {0,1} (zero set proved over any field: B = C c * X^m * (1-X)^n
with c != 0), which is impossible since beta notin S.  The remaining branch is
B_{m,n}(u) = 1: for u in (0,1) the normalized maximum identity says the unique
maximizer is r; uniqueness of the maximizer (or explicit (m,n) choice avoiding the
finite bad set) is not yet in the tree.  Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingReductionActual

/-- Exact parametric reduction statement (named class-B candidate; NOT proved here). -/
def BetaAvoidingReductionStatement : Prop :=
  ∀ (S : Finset ℚ) (β : ℚ), 2 < S.card → β ∉ S →
    ∃ f : ℚ[X], 0 < f.natDegree ∧
      (S.image (fun x => f.eval x)).card < S.card ∧
      (0 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      (1 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      f.eval β ∉ ({0, 1} : Set ℚ) ∧
      f.eval β ∉ S.image (fun x => f.eval x)

/-- Row record: reduction components + exact blocker. -/
def betaAvoidingReductionRows : List (String × String × String) :=
  [ ("affine step min->0, max->1, third point c->r", "A", "REUSED TauCeti exists_card_image_lt (ported, PROVED)")
  , ("f(S) subset {0,1} and card collapse", "A", "REUSED TauCeti card-collapse construction")
  , ("zero branch f(beta)=0 impossible", "A", "PROVED arithmetic: A(beta) in {0,1} iff beta in {min,max} subset S (contradiction)")
  , ("branch B_{m,n}(u) = 1", "BLOCKER", "needs uniqueness of the normalized maximizer for u in (0,1) (or explicit (m,n) avoiding finite bad set); not in tree")
  , ("full BetaAvoidingReductionStatement", "NAMED", "class-B candidate; assignment to parametric core (hull) + S6/S7 one-offs") ]

theorem betaAvoidingReductionRows_length : betaAvoidingReductionRows.length = 5 := rfl

#check BetaAvoidingReductionStatement
#check betaAvoidingReductionRows_length

end LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingReductionActual
end