import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic
import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels

/-! # S746: ordinary O^tri vs the q[2u] root stack

Paper source (IUT I Example 3.5 / Def 3.1):
* ordinary O^tri_{K_v} is the integral monoid O^tri = O^× × N·log(p_v),
  equivalently unit part times a nonnegative p-adic exponent;
* q[1u] has exponent order(q_v), and Def 3.1(c) assumes l is prime to this order;
* a 2l-th root of q[1u] in the ordinary integral monoid would force
  2l | order(q_v), contradicting l ∤ order(q_v);
* the source instead puts q[2u] in O^tri(TX_v), the log/root-stack monoid, not
  in the ordinary integral monoid O^tri_{K_v}.

This file records the ordinary monoid model and the exact no-root theorem.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S746OrdinaryOTriActual

open LeanFormal.IUT

universe u
variable {l : PrimeGeFive}

/-- Ordinary integral monoid O^tri_{K_v}: unit part times a natural p-adic
exponent, matching O^× × N·log(p_v) of [FrdI] Proposition 2.2. -/
structure OrdinaryOTri (K : Type u) [Monoid K] where
  unit : Kˣ
  exponent : Nat

namespace OrdinaryOTri

variable {K : Type u} [Monoid K]

/-- The q-parameter element of exponent n. -/
def ofExponent (u : Kˣ) (n : Nat) : OrdinaryOTri K :=
  ⟨u, n⟩

/-- Power in the ordinary integral monoid. -/
def pow (r : OrdinaryOTri K) (n : Nat) : OrdinaryOTri K :=
  ⟨r.unit ^ n, n * r.exponent⟩

@[simp] theorem pow_exponent (r : OrdinaryOTri K) (n : Nat) :
    (r.pow n).exponent = n * r.exponent := rfl

/-- If 2l does not divide the exponent, the ordinary integral monoid has no
2l-th root of that element. -/
theorem no_twoL_root_of_not_dvd {u : Kˣ} {n : Nat}
    (h : ¬ (2 * l.value ∣ n)) :
    ¬ ∃ r : OrdinaryOTri K, r.pow (2 * l.value) = ofExponent u n := by
  rintro ⟨r, hr⟩
  have hn : 2 * l.value * r.exponent = n := by
    simpa [pow, ofExponent] using congrArg OrdinaryOTri.exponent hr
  exact h ⟨r.exponent, hn.symm⟩

/-- Def 3.1(c) gives l prime to the q-parameter order; hence 2l is not a
divisor of that order. -/
theorem not_twoL_dvd_of_not_l_dvd {n : Nat}
    (h : ¬ l.value ∣ n) : ¬ (2 * l.value ∣ n) := by
  rintro ⟨c, hc⟩
  exact h ⟨2 * c, by rw [hc]; ring⟩

end OrdinaryOTri

/-- Exact paper-faithful conclusion: the ordinary integral O^tri has no
2l-th root of an element whose exponent is prime to l.  The root q[2u] of
IUT I is therefore not in ordinary O^tri_{K_v}; it lives in the log/root-stack
monoid O^tri(TX_v), whose root operation is a separate exact datum. -/
theorem ordinaryOTri_no_q2u_root
    {K : Type u} [Monoid K] (u : Kˣ) (n : Nat)
    (h : ¬ l.value ∣ n) :
    ¬ ∃ r : OrdinaryOTri K,
      (OrdinaryOTri.pow r (2 * l.value)) = OrdinaryOTri.ofExponent u n := by
  exact OrdinaryOTri.no_twoL_root_of_not_dvd
    (OrdinaryOTri.not_twoL_dvd_of_not_l_dvd h)

/-- Root-stack O^tri(TX_v) is not the ordinary integral monoid: it carries an
extra 2l-th root operation.  This is the exact missing carrier datum. -/
structure RootStackOTri (K : Type u) [Monoid K] where
  ordinary : OrdinaryOTri K
  root : Prop
  root_pow : root -> Prop

end LeanFormal.IUT.XiFPaper.S746OrdinaryOTriActual
end
