/- B1 analytic h (route §4.3 L298-334): the target over C and the rational base case.

Direction note (Lead ruling): phi = psiFixed ≫ hPoly with psiFixed = inv ∘ psi, hence
Branch(psiFixed) = inv '' Branch(psi) (P^1 involution lambda |-> lambda^{-1}). The target
below is stated for an abstract finite branch set `Branch : Finset C`, so the caller
plugs in the appropriate presentation; the inversion transport is left to that caller.
-/
import tmp.sheaf.xif.paper.Mzk1G1PsiM2ProducerActual
import tmp.sheaf.xif.paper.Mzk1G1PsiFixedActual
import tmp.sheaf.xif.paper.Mzk1BetaAvoidingBelyiRationalActual
import tmp.sheaf.xif.paper.RestatedLemma24InterfaceActual
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2AnalyticActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

/-- The B1 analytic target over C: a nonconstant rational polynomial q whose finite
critical values lie in {0,1}, which sends the algebraic branch set into {0,1}, and which
keeps 0 out of {0,1}. Since q is polynomial, infinity is automatically a branch value
(total ramification at infinity), so it needs no separate conjunct. -/
def M2AnalyticTarget (Branch : Finset ℂ) : Prop :=
  ∃ q : Polynomial ℚ, 0 < q.natDegree ∧
    (∀ z ∈ Branch, Polynomial.aeval z q ∈ ({0, 1} : Set ℂ)) ∧
    (∀ z : ℂ, Polynomial.aeval z (Polynomial.derivative q) = 0 →
      Polynomial.aeval z q ∈ ({0, 1} : Set ℂ)) ∧
    Polynomial.aeval (0 : ℂ) q ∉ ({0, 1} : Set ℂ)

/-- The aeval of q at 0 is the rational evaluation. -/
theorem aeval_zero_eq (q : Polynomial ℚ) :
    Polynomial.aeval (0 : ℂ) q = ((Polynomial.eval (0 : ℚ) q : ℚ) : ℂ) := by
  rw [Polynomial.aeval_def]
  rw [show (0 : ℂ) = algebraMap ℚ ℂ (0 : ℚ) from by simp]
  rw [Polynomial.eval₂_at_apply]
  simp

/-- Membership of a finite value in the special set, transported to rational evaluation. -/
theorem polyEvalP1_ofFinite_mem_specialSet_iff (q : Polynomial ℚ) (x : ℚ) :
    polyEvalP1 q (P1Point.ofFinite x) ∈ specialSet ℚ ↔
      Polynomial.eval x q = 0 ∨ Polynomial.eval x q = 1 := by
  simp only [polyEvalP1, specialSet, P1Point.ofFinite, P1Point.infty, Option.map_some,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h | h)
    · exact absurd h (by simp)
    · exact Or.inl (Option.some.inj h)
    · exact Or.inr (Option.some.inj h)
  · rintro (h | h)
    · exact Or.inr (Or.inl (by rw [h]))
    · exact Or.inr (Or.inr (by rw [h]))

/-- Base case of the §4.3 recursion (rational end): the target holds for the empty
branch set, extracted unconditionally from the M1 base case `mzk1Lemma24Target_of_zero`. -/
theorem m2AnalyticTarget_empty : M2AnalyticTarget ∅ := by
  obtain ⟨q, hdeg, -, hβ, hcv, -⟩ := LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2ProducerActual.mzk1Lemma24Target_of_zero
    (∅ : Finset (P1Point ℚ)) (by simp)
  refine ⟨q, hdeg, ?_, ?_, ?_⟩
  · intro z hz
    simp at hz
  · intro z hz
    exact hcv ⟨z, by omega, hz, rfl⟩
  · intro hmem
    rw [aeval_zero_eq q] at hmem
    have hℚ : Polynomial.eval (0 : ℚ) q = 0 ∨ Polynomial.eval (0 : ℚ) q = 1 := by
      rcases hmem with h | h
      · have h' : (↑(Polynomial.eval (0 : ℚ) q) : ℂ) = 0 := by simpa using h
        exact Or.inl (by exact_mod_cast h')
      · have h' : (↑(Polynomial.eval (0 : ℚ) q) : ℂ) = 1 := by simpa using h
        exact Or.inr (by exact_mod_cast h')
    apply hβ
    rw [polyEvalP1_ofFinite_mem_specialSet_iff]
    exact hℚ
#print axioms aeval_zero_eq
#print axioms polyEvalP1_ofFinite_mem_specialSet_iff
#print axioms m2AnalyticTarget_empty
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2AnalyticActual