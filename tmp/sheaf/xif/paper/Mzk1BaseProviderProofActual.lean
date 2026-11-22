import tmp.sheaf.xif.paper.Mzk1Lemma22InductionProofActual
import tmp.sheaf.xif.paper.Mzk1BetaAvoidingBelyiRationalActual
import Mathlib.Tactic

/-! # Mzk1BaseProviderProofActual — PROOF of the |S| ≤ 3 base provider of [Mzk1] Lemma 2.2 (F=Q)

This file discharges the named input `BaseProviderStatement` of
`Mzk1Lemma22InductionProofActual`:

  `∀ S β, S.card ≤ 3 → Lemma22Hypotheses S β → ∃ f : ℚ[X], Good f S β`.

## Key observation (why the base case is genuinely elementary)

`Lemma22Hypotheses S β` forces `P1Point.infty ∈ S` (second conjunct), and the paper's
Belyi target set is `specialSet ℚ = {∞, 0, 1}`: on `P^1` a polynomial fixes `∞`, so the
point `∞ ∈ S` is carried into the target by *every* polynomial.  Consequently, for
`S.card ≤ 3` at most **two** finite points of `S` remain to be handled, and the already
proved `Mzk1BetaAvoidingBelyiRationalActual.exists_betaAvoiding_card_le_two` supplies a
nonconstant `q : ℚ[X]` with `q(T) ⊆ {0,1}`, `q(b) ∉ {0,1}` and all critical values in
`{0,1}`, for the finite part `T` of `S` and the finite point `b` with `β = ofFinite b`
(β is finite because β ∉ S while ∞ ∈ S).

Thus the Belyi three-point step is *not* needed for the base provider; it is needed only
for the step provider (`3 < S.card`, where `S` has at least two finite points after ∞).

No sorry, no new axioms, no PUnit/True placeholders.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1BaseProviderProofActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.RestatedLemma22InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22InductionProofActual
open LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingBelyiRationalActual

/-! ### The finite part of a finite set of rational points -/

/-- The finite points of `S`, read as rational numbers.  `∞` is erased *before* the
projection, so the junk value `0` of the projection is never used on a genuine point. -/
def finiteRatSet (S : Finset (P1Point ℚ)) : Finset ℚ :=
  (S.erase P1Point.infty).image fun p => match p with
    | none => 0
    | some x => x

/-- A finite member of `S` is a member of the finite part. -/
theorem mem_finiteRatSet_of_mem {S : Finset (P1Point ℚ)} {x : ℚ}
    (h : P1Point.ofFinite x ∈ S) : x ∈ finiteRatSet S := by
  refine Finset.mem_image.mpr ⟨P1Point.ofFinite x, ?_, rfl⟩
  exact Finset.mem_erase.mpr ⟨P1Point.ofFinite_ne_infty x, h⟩

/-- Every member of the finite part is a finite member of `S`. -/
theorem ofFinite_mem_of_mem_finiteRatSet {S : Finset (P1Point ℚ)} {x : ℚ}
    (h : x ∈ finiteRatSet S) : P1Point.ofFinite x ∈ S := by
  unfold finiteRatSet at h
  obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp h
  rw [Finset.mem_erase] at hp
  obtain ⟨hpinf, hpS⟩ := hp
  rcases p with _ | y
  · exact absurd rfl hpinf
  · have hyx : y = x := hpx
    rw [← hyx]
    exact hpS

/-- The finite part has at most as many points as `S` with `∞` removed. -/
theorem finiteRatSet_card_le_erase (S : Finset (P1Point ℚ)) :
    (finiteRatSet S).card ≤ (S.erase P1Point.infty).card := by
  simp only [finiteRatSet]
  exact Finset.card_image_le

/-- **Cardinality bound:** if `S.card ≤ 3` and `∞ ∈ S`, the finite part of `S` has at most
two elements.  (The point `∞` accounts for one of the three points.) -/
theorem finiteRatSet_card_le_two (S : Finset (P1Point ℚ))
    (hinf : P1Point.infty ∈ S) (hcard : S.card ≤ 3) : (finiteRatSet S).card ≤ 2 := by
  have h1 := finiteRatSet_card_le_erase S
  have h2 : (S.erase P1Point.infty).card = S.card - 1 := Finset.card_erase_of_mem hinf
  omega

/-! ### Membership in the Belyi target set `{∞, 0, 1}` -/

/-- `∞` (the point `none` of `Option ℚ`) belongs to the target set. -/
theorem none_mem_specialSet : (none : P1Point ℚ) ∈ specialSet ℚ := by
  simp [specialSet, P1Point.infty, P1Point.ofFinite]

/-- A finite point `some x` belongs to the target set iff its coordinate is 0 or 1. -/
theorem some_mem_specialSet_iff {x : ℚ} :
    (some x : P1Point ℚ) ∈ specialSet ℚ ↔ x = 0 ∨ x = 1 := by
  simp [specialSet, P1Point.infty, P1Point.ofFinite]

/-- A finite point `ofFinite x` belongs to the target set iff its coordinate is 0 or 1. -/
theorem ofFinite_mem_specialSet_iff {x : ℚ} :
    P1Point.ofFinite x ∈ specialSet ℚ ↔ x = 0 ∨ x = 1 := by
  simp [specialSet, P1Point.infty, P1Point.ofFinite]

/-! ### The base provider -/

/-- **PROVED: Good polynomial for `S.card ≤ 3` under the paper hypotheses.** -/
theorem exists_good_of_card_le_three (S : Finset (P1Point ℚ)) (β : P1Point ℚ)
    (hcard : S.card ≤ 3) (H : Lemma22Hypotheses S β) : ∃ f : ℚ[X], Good f S β := by
  rcases β with _ | b
  · -- β = ∞ is impossible: ∞ ∈ S while β ∉ S
    exact absurd H.2.1 H.2.2.2.1
  · -- β = ofFinite b: only the finite part of S matters
    have hTcard : (finiteRatSet S).card ≤ 2 := finiteRatSet_card_le_two S H.2.1 hcard
    have hbT : b ∉ finiteRatSet S := by
      intro hb
      exact H.2.2.2.1 (ofFinite_mem_of_mem_finiteRatSet hb)
    obtain ⟨q, hqdeg, hqC, hqT, hqb0, hqb1⟩ :=
      exists_betaAvoiding_card_le_two (finiteRatSet S) hTcard b hbT
    refine ⟨q, ?_, ?_, ?_, ?_⟩
    · -- nonconstant
      omega
    · -- S is carried into the Belyi target set
      intro p hp
      rcases p with _ | x
      · have hpoly : polyEvalP1 q (none : P1Point ℚ) = none := rfl
        rw [hpoly]
        exact none_mem_specialSet
      · have hpoly : polyEvalP1 q (some x) = some (q.eval x) := rfl
        rw [hpoly, some_mem_specialSet_iff]
        exact hqT x (mem_finiteRatSet_of_mem hp)
    · -- β is carried outside the Belyi target set
      intro hmem
      have hpoly : polyEvalP1 q (some b) = some (q.eval b) := rfl
      rw [hpoly, some_mem_specialSet_iff] at hmem
      rcases hmem with h' | h'
      · exact hqb0 h'
      · exact hqb1 h'
    · -- all critical values over ℂ lie in {0,1}
      intro z hz hd
      rcases hqC z hd with h | h
      · exact hz (by rw [h]; simp)
      · exact hz (by rw [h]; simp)

/-- **The |S| ≤ 3 base provider of [Mzk1] Lemma 2.2 (F = Q component) — PROVED.**
This is the named input `BaseProviderStatement` consumed by
`mzk1Lemma22_induction_conditional`. -/
theorem baseProvider_holds :
    LeanFormal.IUT.XiFPaper.Mzk1Lemma22InductionProofActual.BaseProviderStatement := by
  intro S β hcard H
  exact exists_good_of_card_le_three S β hcard H

/-- Row record: (component, Lean evidence, status). -/
def baseProviderRows : List (String × String × String) :=
  [ ("finite part of S (∞ erased, projected to ℚ)", "finiteRatSet + mem/ofFinite_mem lemmas", "DEFINED/PROVED"),
    ("|finite part| ≤ 2 when |S| ≤ 3 and ∞ ∈ S", "finiteRatSet_card_le_two", "PROVED"),
    ("∞ ∈ {∞,0,1} and some/ofFinite x ∈ {∞,0,1} ↔ x ∈ {0,1}", "none_mem_specialSet / some_mem_specialSet_iff / ofFinite_mem_specialSet_iff", "PROVED"),
    ("basis: beta-avoiding Belyi with CV ⊆ {0,1} for ≤ 2 rational points", "Mzk1BetaAvoidingBelyiRationalActual.exists_betaAvoiding_card_le_two", "REUSED (PROVED there)"),
    ("Good polynomial for |S| ≤ 3 under Lemma22Hypotheses", "exists_good_of_card_le_three", "PROVED"),
    ("named base input of the Lemma 2.2 induction", "baseProvider_holds : BaseProviderStatement", "PROVED") ]

theorem baseProviderRows_length : baseProviderRows.length = 6 := rfl

#check exists_good_of_card_le_three
#check baseProvider_holds
#print axioms baseProvider_holds

end LeanFormal.IUT.XiFPaper.Mzk1BaseProviderProofActual
end
