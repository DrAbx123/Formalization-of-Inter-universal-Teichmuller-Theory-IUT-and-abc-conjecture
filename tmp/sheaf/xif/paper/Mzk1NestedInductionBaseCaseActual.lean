import Mathlib
import tmp.sheaf.xif.paper.Mzk1NestedInductionActual
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1NestedInductionBaseCaseActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.PaperScopeLemma24Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

abbrev Qbar : Type := AlgebraicClosure ℚ

/-- A point of P1(Qbar) of degree at most 1 is rational (its finite part lies in the image
of Q). -/
theorem exists_rat_eq_of_degP_le_one (p : P1Point Qbar) (hp : degP p ≤ 1) :
    ∃ r : P1Point ℚ, castRatPoint r = p := by
  cases p with
  | none => exact ⟨P1Point.infty, rfl⟩
  | some z =>
    have hdeg : degQ z ≤ 1 := hp
    have hpos : 1 ≤ degQ z := degQ_pos z
    have h1 : degQ z = 1 := le_antisymm hdeg hpos
    obtain ⟨r, hr⟩ := (minpoly.natDegree_eq_one_iff (A := ℚ) (B := Qbar) (x := z)).mp h1
    exact ⟨P1Point.ofFinite r, by
      show P1Point.ofFinite (algebraMap ℚ Qbar r) = P1Point.ofFinite z
      rw [hr]⟩

/-- **Base case of the nested induction, PROVED**: for every state whose points all have
degree at most 1 (i.e. all points rational) and every beta outside S, the paper-scope
target holds.  Witness: the identity polynomial f = X over Qbar and the rational target
set S_phi = rationalisation of S; the value at beta equals beta, which is outside S, and
the identity has no critical points, so the critical-value conjunct is vacuous. -/
theorem baseCaseProvider_proved : BaseCaseProvider := by
  classical
  intro S beta hbeta hmax
  -- rationalise every point of S
  let rat : (p : P1Point Qbar) → p ∈ S → P1Point ℚ := fun p hp =>
    Classical.choose (exists_rat_eq_of_degP_le_one p
      (le_trans (Finset.le_sup (s := S) (f := degP) hp) hmax))
  have hrat : ∀ (p : P1Point Qbar) (hp : p ∈ S), castRatPoint (rat p hp) = p := fun p hp =>
    Classical.choose_spec (exists_rat_eq_of_degP_le_one p
      (le_trans (Finset.le_sup (s := S) (f := degP) hp) hmax))
  let Sphi : Finset (P1Point ℚ) := S.attach.image (fun p => rat p.1 p.2)
  have hmem : ∀ r : P1Point ℚ, r ∈ Sphi ↔ ∃ p : P1Point Qbar, ∃ hp : p ∈ S, rat p hp = r := by
    intro r
    constructor
    · intro hr
      obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hr
      exact ⟨p.1, p.2, hp⟩
    · rintro ⟨p, hp, rfl⟩
      exact Finset.mem_image.mpr ⟨⟨p, hp⟩, Finset.mem_attach S ⟨p, hp⟩, rfl⟩
  refine ⟨Sphi, Polynomial.X, ?_, ?_, ?_, ?_⟩
  · simp
  · intro p hp
    refine ⟨rat p hp, ?_, ?_⟩
    · rw [hmem]
      exact ⟨p, hp, rfl⟩
    · show polyEvalP1K (Polynomial.X : Polynomial Qbar) p = castRatPoint (rat p hp)
      rw [hrat p hp]
      show polyEvalP1K (Polynomial.X : Polynomial Qbar) p = p
      simp [polyEvalP1K, Polynomial.eval_X]
  · rintro ⟨r, hrS, hrβ⟩
    obtain ⟨p, hp, rfl⟩ := (hmem r).mp hrS
    have : beta = p := by
      have h1 : polyEvalP1K (Polynomial.X : Polynomial Qbar) beta = beta := by
        simp [polyEvalP1K, Polynomial.eval_X]
      rw [h1, hrat p hp] at hrβ
      exact hrβ
    exact hbeta (this ▸ hp)
  · intro z hz
    exfalso
    have hder : Polynomial.aeval z (Polynomial.derivative (Polynomial.X : Polynomial Qbar)) =
        (1 : Qbar) := by simp
    rw [hder] at hz
    exact one_ne_zero hz

/-- Status: the base case of the Problem C nested induction is PROVED unconditionally
for all-rational states (identity polynomial witness).  No closure of the paper statement
(the StepProvider/map layer remains named); registry frozen 14041. -/
def NestedInductionBaseCaseStatus : Audit.Obligation :=
  { id := "MZK1.problemC.base-case"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 163-206; Lead A410/A411 assignment"
    status := Audit.VerificationStatus.proved
    note := "PROVED: baseCaseProvider_proved — BaseCaseProvider (all-rational states, maxDegP <= 1) holds unconditionally: rationalise the points of S by minpoly.natDegree_eq_one_iff + degQ_pos, take f = X over Qbar and S_phi = rationalisation of S; f(S) = S into S_phi, f(beta) = beta outside S_phi since beta not in S, and f' = 1 has no critical points so the critical-value conjunct is vacuous. Supporting lemma exists_rat_eq_of_degP_le_one. This discharges the base provider of Mzk1NestedInductionActual.paperScopeLemma24Statement_of_providers; the StepProvider (geometric map layer) remains named. No closure; binding HOLD; gate NOT PASSED; registry frozen 14041."
    dependsOn := [ "MZK1.problemC.nested-induction" ]
    sorryItems := [ "StepProvider (P1 map layer; named)" ] }

#check baseCaseProvider_proved
end LeanFormal.IUT.XiFPaper.Mzk1NestedInductionBaseCaseActual
end