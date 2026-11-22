/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import tmp.sheaf.xif.paper.S2583FactorDegreeActual

/-!
# S2565: the degree-twelve Rabin criterion over a finite field

This file records, in the namespace `S2565Mod613RabinCriterionActual`, the
generic degree-twelve Rabin criterion that was first written out in
`S2540Mod613CertificateActual`:

* `S2540X_pow_dvd`: if `d ∣ m` then `X^(q^d) - X ∣ X^(q^m) - X`;
* `S2540irreducible_of_degree_twelve`: if `f` has degree twelve, divides
  `X^(q^12) - X`, and is coprime to `X^(q^4) - X` and `X^(q^6) - X`, then `f`
  is irreducible.

The copy is deliberately independent of `S2540Mod613CertificateActual` and of
the chain-1 development (`S2564Chain1*`, `S2556Mod613Chain1Actual`).  The only
imports are Mathlib and `S2583FactorDegreeActual`, which supplies the
factor-degree input

`irreducible_dvd_X_pow_card_pow_sub_X`: an irreducible monic polynomial `g`
over a finite field divides `X^(q ^ g.natDegree) - X`.

Since `S2583FactorDegreeActual` states that bound for *monic* `g`, the proof
below takes the monic irreducible factor of `f` supplied by
`Polynomial.exists_monic_irreducible_factor` (Mathlib) instead of an arbitrary
irreducible factor; the rest of the argument is the one from S2540.  The
`S2540...` names are retained inside the namespace so that consumers written
against the S2540 statement can be reused verbatim; `S2565...` aliases are
provided as well.

The intended consumer is the mod-613 irreducibility of the monic normalization
`G` of `S2554Mod613ChainDataActual`, using the Frobenius chain data
`T1, ..., T12 = X` and Bezout identities at the exponents `4` and `6`.
-/

noncomputable section
open Polynomial

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.S2565Mod613RabinCriterionActual

/-! ## The divisibility step -/

/-- If `d` divides `m` then `X^(q^d) - X` divides `X^(q^m) - X`. -/
lemma S2540X_pow_dvd {K : Type*} [CommRing K] {d m : ℕ} (h : d ∣ m) :
    ((X : K[X]) ^ Nat.card K ^ d - X) ∣ ((X : K[X]) ^ Nat.card K ^ m - X) :=
  dvd_pow_pow_sub_self_of_dvd (r := (X : K[X])) (p := Nat.card K) h

/-! ## The degree-twelve Rabin criterion -/

/-- Rabin criterion, degree 12.  If `f` has degree twelve, every root of `f`
lies in `GF(q^12)`, and `f` has no root in `GF(q^4)` or `GF(q^6)`, then `f` is
irreducible.

The factor-degree input `g ∣ X^(q ^ g.natDegree) - X` for an irreducible monic
`g` is `S2583FactorDegreeActual.irreducible_dvd_X_pow_card_pow_sub_X`. -/
theorem S2540irreducible_of_degree_twelve {K : Type*} [Field K] [Fintype K] {f : K[X]}
    (hdeg : f.natDegree = 12)
    (hdvd : f ∣ (X : K[X]) ^ Nat.card K ^ 12 - X)
    (h4 : IsCoprime f ((X : K[X]) ^ Nat.card K ^ 4 - X))
    (h6 : IsCoprime f ((X : K[X]) ^ Nat.card K ^ 6 - X)) :
    Irreducible f := by
  classical
  by_contra hf
  have hf0 : f ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hfunit : ¬ IsUnit f := by
    intro hu
    have h0 := natDegree_eq_zero_of_isUnit hu
    omega
  obtain ⟨g, hg_monic, hg_irr, hg_dvd⟩ :=
    Polynomial.exists_monic_irreducible_factor f hfunit
  have hg_dvd_E : g ∣ (X : K[X]) ^ Nat.card K ^ 12 - X := hg_dvd.trans hdvd
  have hdvd12 : g.natDegree ∣ 12 :=
    Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hg_irr hg_dvd_E
  have hgpos : 0 < g.natDegree := Irreducible.natDegree_pos hg_irr
  have hgle : g.natDegree ≤ 12 := by
    rw [← hdeg]
    exact natDegree_le_of_dvd hg_dvd hf0
  have hgne : g.natDegree ≠ 12 := by
    intro h12
    have hassoc : Associated g f := associated_of_dvd_of_natDegree_le hg_dvd hf0 (by omega)
    exact hf (hassoc.irreducible hg_irr)
  -- The factor-degree bound from S2583FactorDegreeActual, in Nat.card form.
  have hgfac : g ∣ (X : K[X]) ^ (Nat.card K ^ g.natDegree) - X := by
    have h :=
      LeanFormal.IUT.XiFPaper.S2583FactorDegreeActual.irreducible_dvd_X_pow_card_pow_sub_X
        (K := K) (g := g) hg_irr hg_monic
    simpa [Nat.card_eq_fintype_card] using h
  set d := g.natDegree with hddef
  have hdvd' : d ∣ 12 := by simpa [hddef] using hdvd12
  have hlt' : d < 12 := by simpa [hddef] using lt_of_le_of_ne hgle hgne
  have hpos' : 0 < d := by simpa [hddef] using hgpos
  have hcases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 6 := by
    interval_cases d <;> norm_num at hdvd' <;> norm_num
  rcases hcases with h1 | h2 | h3 | h4d | h6d
  · have hgd : g.natDegree = 1 := by omega
    have hg1 : g ∣ (X : K[X]) ^ Nat.card K ^ 1 - X := by simpa [hgd] using hgfac
    have hg6 : g ∣ (X : K[X]) ^ Nat.card K ^ 6 - X :=
      hg1.trans (S2540X_pow_dvd (K := K) (d := 1) (m := 6) (by norm_num))
    exact hg_irr.not_isUnit (h6.isUnit_of_dvd' hg_dvd hg6)
  · have hgd : g.natDegree = 2 := by omega
    have hg2 : g ∣ (X : K[X]) ^ Nat.card K ^ 2 - X := by simpa [hgd] using hgfac
    have hg6 : g ∣ (X : K[X]) ^ Nat.card K ^ 6 - X :=
      hg2.trans (S2540X_pow_dvd (K := K) (d := 2) (m := 6) (by norm_num))
    exact hg_irr.not_isUnit (h6.isUnit_of_dvd' hg_dvd hg6)
  · have hgd : g.natDegree = 3 := by omega
    have hg3 : g ∣ (X : K[X]) ^ Nat.card K ^ 3 - X := by simpa [hgd] using hgfac
    have hg6 : g ∣ (X : K[X]) ^ Nat.card K ^ 6 - X :=
      hg3.trans (S2540X_pow_dvd (K := K) (d := 3) (m := 6) (by norm_num))
    exact hg_irr.not_isUnit (h6.isUnit_of_dvd' hg_dvd hg6)
  · have hgd : g.natDegree = 4 := by omega
    have hg4 : g ∣ (X : K[X]) ^ Nat.card K ^ 4 - X := by simpa [hgd] using hgfac
    exact hg_irr.not_isUnit (h4.isUnit_of_dvd' hg_dvd hg4)
  · have hgd : g.natDegree = 6 := by omega
    have hg6 : g ∣ (X : K[X]) ^ Nat.card K ^ 6 - X := by simpa [hgd] using hgfac
    exact hg_irr.not_isUnit (h6.isUnit_of_dvd' hg_dvd hg6)

/-! ## Aliases under the S2565 prefix -/

/-- `S2565X_pow_dvd` is `S2540X_pow_dvd`, named for this file. -/
lemma S2565X_pow_dvd {K : Type*} [CommRing K] {d m : ℕ} (h : d ∣ m) :
    ((X : K[X]) ^ Nat.card K ^ d - X) ∣ ((X : K[X]) ^ Nat.card K ^ m - X) :=
  S2540X_pow_dvd h

/-- `S2565irreducible_of_degree_twelve` is the degree-twelve Rabin criterion,
named for this file. -/
theorem S2565irreducible_of_degree_twelve {K : Type*} [Field K] [Fintype K] {f : K[X]}
    (hdeg : f.natDegree = 12)
    (hdvd : f ∣ (X : K[X]) ^ Nat.card K ^ 12 - X)
    (h4 : IsCoprime f ((X : K[X]) ^ Nat.card K ^ 4 - X))
    (h6 : IsCoprime f ((X : K[X]) ^ Nat.card K ^ 6 - X)) :
    Irreducible f :=
  S2540irreducible_of_degree_twelve hdeg hdvd h4 h6

#print axioms S2540X_pow_dvd

#print axioms S2540irreducible_of_degree_twelve

#print axioms S2565irreducible_of_degree_twelve

end LeanFormal.IUT.XiFPaper.S2565Mod613RabinCriterionActual

end
