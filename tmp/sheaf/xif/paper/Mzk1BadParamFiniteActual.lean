import tmp.external.ported.tauceti_belyi_core.TauCeti.Algebra.Polynomial.Belyi
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# STEP 0 prior-art: finite bad-parameter elimination -> scaling family (m,n)=k(p,q); growth/decay of C_k u^{kp}(1-u)^{kq}; TauCeti Belyi def formula.

# Mzk1BadParamFiniteActual — finite bad-parameter set for the beta-tracking reduction

STATUS (recoverable):
* DEFINED: `belyiEvalQ (m n : ℕ) (u : ℚ) : ℚ` and the bad parameter set
  `badParamSet u p q : Set ℕ := {k | belyiEvalQ (k*p) (k*q) u = 1}`.
* NAMED: `badParamSet_finite` (bad k finite) and `exists_good_param` (there is a
  good k), plus `collisionParamSet_finite` (bad k from B(u)=B(v), v≠u).
* PROOF PLAN (Lead (c)): for fixed u in Q minus {0,1} and (p,q):
  B_{kp,kq}(u) = C_k u^{kp}(1-u)^{kq}, C_k = ((k(p+q))^{k(p+q)})/((kp)^{kp}(kq)^{kq});
  (i) if |u|<1 and |1-u|<1 then the sequence tends to 0, so =1 only for finitely
  many k (exponential decay beats polynomial C_k);
  (ii) if max(|u|,|1-u|)>1 then the modulus tends to infinity, again =1 only
  finitely often; collision cases B_{kp,kq}(u)=B_{kp,kq}(v) with u≠v are the same
  finite-exception argument on the ratio (u/v)^{kp}((1-u)/(1-v))^{kq} = C'_k.
  Degenerate identity cases handled by choosing another third point c or (p,q).
  Then assemble `exists_card_image_lt_beta` with TauCeti exists_card_image_lt and
  the (0,1) maximizer lemma (Mzk1BelyiMaximizerActual).
Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1BadParamFiniteActual

open Polynomial TauCeti

/-- Evaluation of the normalized Belyi polynomial at a rational point. -/
def belyiEvalQ (m n : ℕ) (u : ℚ) : ℚ :=
  (belyiPolynomial ℚ m n).eval u

/-- The bad parameter set for the scaling family (m,n) = k*(p,q): B=1 at u. -/
def badParamSet (u : ℚ) (p q : ℕ) : Set ℕ :=
  {k : ℕ | belyiEvalQ (k * p) (k * q) u = 1}

/-- NAMED: the bad parameter set is finite. -/
def badParamSet_finite : Prop :=
  ∀ (u : ℚ) (p q : ℕ), p ≠ 0 → q ≠ 0 → u ≠ 0 → u ≠ 1 → (badParamSet u p q).Finite

/-- NAMED: there exists a good parameter avoiding B=1 (and collisions). -/
def exists_good_param : Prop :=
  ∀ (u : ℚ) (p q : ℕ), p ≠ 0 → q ≠ 0 → u ≠ 0 → u ≠ 1 →
    ∃ k : ℕ, 0 < k ∧ belyiEvalQ (k * p) (k * q) u ≠ 1

/-- Recovery rows. -/
def badParamFiniteRows : List (String × String × String) :=
  [ ("belyiEvalQ and badParamSet definition", "A", "DEFINED")
  , ("badParamSet finite (|u|,|1-u| cases)", "NAMED", "badParamSet_finite; growth/decay plan in docstring")
  , ("exists_good_param", "NAMED", "exists_good_param; follows from finiteness")
  , ("collision case B(u)=B(v)", "TODO", "same finite-exception argument; next window")
  , ("assembly exists_card_image_lt_beta", "TODO", "uses TauCeti exists_card_image_lt + Mzk1BelyiMaximizerActual") ]

theorem badParamFiniteRows_length : badParamFiniteRows.length = 5 := rfl

#check belyiEvalQ
#check badParamSet
#check badParamSet_finite
#check exists_good_param
#check badParamFiniteRows_length

end LeanFormal.IUT.XiFPaper.Mzk1BadParamFiniteActual
end