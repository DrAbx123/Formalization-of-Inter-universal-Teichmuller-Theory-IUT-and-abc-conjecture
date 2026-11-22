import tmp.sheaf.xif.paper.S1366PrePsiSeparabilityFix
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1420PrePsiDerivativeActual

open Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1298TorsionClauseActual
open LeanFormal.IUT.XiFPaper.S1329RankTwoTorsionBasisActual
open LeanFormal.IUT.XiFPaper.S1366PrePsiSeparabilityFix

/-!
# S1420: the derivative / gcd / Squarefree route to separability of preΨₙ

The target is `S1366GenericOddPreΨSeparableInput`:

`∀ (F) [Field F] [CharZero F] (W : WeierstrassCurve F) [W.IsElliptic] (n : ℤ),
  ¬ Even n → n ≠ 0 → (W.preΨ n).Separable`.

S1396 closed the *counting* route (torsion detection + `Nat.card` of the `n`-torsion),
via the S1366 theorem `s1366Separable_of_detection_and_card`.  This file instead works
the *derivative / gcd / squarefree* route and does not mention torsion points,
`Nat.card`, or any counting argument at all.

## What this file proves (all unconditional)

1. **The derivative criterion** (`separable_iff_aeval_derivative_ne_zero`), over an
   arbitrary field `F`: a polynomial `p : F[X]` is separable iff its derivative does
   not vanish at any of its roots in the algebraic closure.  Mathlib has the easy
   direction (`Separable.aeval_derivative_ne_zero`); the converse — no double root
   over the algebraic closure implies `IsCoprime p p'` — is proved here from
   `nodup_aroots_iff_of_splits` / `nodup_roots_iff_of_splits` and the
   root-multiplicity/derivative API.

2. **The target is exactly the gcd condition.**  `Polynomial.Separable f` *is*
   `IsCoprime f (derivative f)` (Mathlib `Polynomial.separable_def`), so
   `s1420_generic_iff_isCoprime` shows the target is *definitionally* the statement
   `gcd(preΨₙ, preΨₙ') = 1`; there is no weakening in passing to the gcd form.

3. **The target is exactly Squarefreeness in characteristic zero.**
   `PerfectField.ofCharZero` makes every characteristic-zero field perfect, so
   `PerfectField.separable_iff_squarefree` gives
   `Squarefree (W.preΨ n) ↔ (W.preΨ n).Separable`, and
   `squarefree_iff_aeval_derivative_ne_zero` reads squarefreeness as "the derivative
   does not vanish at any root in the algebraic closure".

4. **The target is exactly the pointwise derivative statement**
   `S1420PrePsiDerivativeNonvanishing`: for every odd nonzero `n`, no root of
   `preΨₙ` in `AlgebraicClosure F` is a root of the derivative.  This is the *exact
   first algebraic lemma* of the derivative route: by (1) it is equivalent, not merely
   sufficient, for the target (`s1420_nonvanishing_iff_generic`).

5. **Unconditional derivative facts for `preΨ`:**
   * `s1420_ΨSq_eq_preΨ_sq`: for odd `n`, `ΨSqₙ = preΨₙ²`;
   * `s1420_derivative_ΨSq_eq`: the derivative formula
     `(ΨSqₙ)' = 2 · preΨₙ · preΨₙ'` for odd `n`, over any commutative ring;
   * `s1420_derivative_preΨ_ne_zero`: for odd `n` with `(n : F) ≠ 0` and
     `|n| > 2`, `preΨₙ' ≠ 0` (its degree is `(|n|² - 1)/2 ≥ 1`);
   * `s1420_nonvanishing_one`, `s1420_nonvanishing_neg_one`: the pointwise statement
     holds at `n = ±1`, where `preΨ_{±1} = ±1`.

6. **Route bridges.**  `isCoprime_derivative_iff_no_common_root` is the classical gcd
   criterion (coprime to the derivative iff no common root in the algebraic closure);
   and, assuming the target, `s1420_aroots_nodup_and_card_of_generic` derives the exact
   root count — `preΨₙ` has `(|n|² - 1)/2` pairwise distinct roots in the algebraic
   closure — with no counting argument and no torsion input.

## What is *not* proved here

`S1420PrePsiDerivativeNonvanishing` itself is not inhabited in this file.  By (4) it
is exactly the target, so nothing is hidden: the remaining algebraic content is the
simplicity of the roots of `preΨₙ`, equivalently a Bezout certificate
`∃ a b : F[X], a * preΨₙ + b * preΨₙ' = 1`.  No `sorry`, no axiom, no placeholder
is used; the file is a complete proof of everything it states.

## References

* [J Silverman, The Arithmetic of Elliptic Curves][silverman2009], III.6.4.
* Mathlib: `Polynomial.Separable`, `Polynomial.nodup_roots_iff_of_splits`,
  `PerfectField.separable_iff_squarefree`, `WeierstrassCurve.natDegree_preΨ`.
-/

/-! ## 1. The derivative criterion for separability -/

/-- **The derivative criterion.**  Over an arbitrary field, a polynomial is separable
if and only if its derivative does not vanish at any of its roots in the algebraic
closure.

The forward direction is Mathlib's `Separable.aeval_derivative_ne_zero`.  For the
converse, if `x` is a double root then `1 < rootMultiplicity x (p.map _)`, so both
`p.map _` and its derivative vanish at `x` by the iterate-derivative criterion for
root multiplicity. -/
theorem separable_iff_aeval_derivative_ne_zero {F : Type*} [Field F] (p : F[X]) :
    p.Separable ↔
      ∀ x : AlgebraicClosure F, aeval x p = 0 → aeval x (derivative p) ≠ 0 := by
  classical
  refine ⟨fun h x hx => h.aeval_derivative_ne_zero hx, fun h => ?_⟩
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact (h 0 (by simp)) (by simp)
  have hsplit : (p.map (algebraMap F (AlgebraicClosure F))).Splits := IsAlgClosed.splits _
  have hiff : (p.map (algebraMap F (AlgebraicClosure F))).roots.Nodup ↔ p.Separable := by
    rw [nodup_roots_iff_of_splits
      (Polynomial.map_ne_zero (f := algebraMap F (AlgebraicClosure F)) hp0) hsplit,
      separable_map]
  rw [← hiff, Multiset.nodup_iff_count_le_one]
  intro x
  by_contra hx
  rw [not_le] at hx
  rw [Polynomial.count_roots] at hx
  refine h x ?_ ?_
  · rw [aeval_def, Polynomial.eval₂_eq_eval_map]
    simpa using Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity
      (p := p.map (algebraMap F (AlgebraicClosure F))) (t := x) (n := 0) (by omega)
  · rw [aeval_def, Polynomial.eval₂_eq_eval_map, ← Polynomial.derivative_map]
    simpa using Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity
      (p := p.map (algebraMap F (AlgebraicClosure F))) (t := x) (n := 1) (by omega)

/-- **The gcd criterion in classical form.**  A polynomial is coprime to its derivative
if and only if no point of the algebraic closure is a common root of the two. -/
theorem isCoprime_derivative_iff_no_common_root {F : Type*} [Field F] (p : F[X]) :
    IsCoprime p (derivative p) ↔
      ∀ x : AlgebraicClosure F, ¬(aeval x p = 0 ∧ aeval x (derivative p) = 0) := by
  rw [← separable_def, separable_iff_aeval_derivative_ne_zero]
  constructor
  · rintro h x ⟨h1, h2⟩
    exact h x h1 h2
  · intro h x hx
    exact fun hx' => h x ⟨hx, hx'⟩

/-! ## 2. The target in gcd and Squarefree form -/

/-- **The gcd form of the target.**  `Polynomial.Separable f` is *defined* as
`IsCoprime f (derivative f)`, i.e. as `gcd(f, f') = 1`.  So the derivative/gcd route
is not a weakening of the target: this is an equivalence, with no content added. -/
theorem s1420_generic_iff_isCoprime :
    S1366GenericOddPreΨSeparableInput ↔
      (∀ (F : Type) [Field F] [CharZero F]
        (W : WeierstrassCurve F) [W.IsElliptic] (n : ℤ),
        ¬ Even n → n ≠ 0 → IsCoprime (W.preΨ n) (derivative (W.preΨ n))) := by
  constructor
  · intro h F _ _ W _ n hodd hn
    exact (separable_def (W.preΨ n)).mp (h F W n hodd hn)
  · intro h F _ _ W _ n hodd hn
    exact (separable_def (W.preΨ n)).mpr (h F W n hodd hn)

/-- **The Bezout form of the exact first algebraic lemma.**  `preΨₙ` is separable iff
there is an explicit certificate `a * preΨₙ + b * preΨₙ' = 1`.  This is the concrete
form in which a derivative/gcd proof would have to produce its input. -/
theorem s1420_generic_iff_bezout :
    S1366GenericOddPreΨSeparableInput ↔
      (∀ (F : Type) [Field F] [CharZero F]
        (W : WeierstrassCurve F) [W.IsElliptic] (n : ℤ),
        ¬ Even n → n ≠ 0 →
          ∃ a b : F[X], a * W.preΨ n + b * derivative (W.preΨ n) = 1) := by
  constructor
  · intro h F _ _ W _ n hodd hn
    exact (separable_def' (W.preΨ n)).mp (h F W n hodd hn)
  · intro h F _ _ W _ n hodd hn
    exact (separable_def' (W.preΨ n)).mpr (h F W n hodd hn)

/-- **Squarefree form in characteristic zero.**  A characteristic-zero field is perfect,
so `Squarefree` and `Separable` coincide for every polynomial over it. -/
theorem s1420_squarefree_iff_separable {F : Type*} [Field F] [CharZero F]
    (W : WeierstrassCurve F) (n : ℤ) :
    Squarefree (W.preΨ n) ↔ (W.preΨ n).Separable :=
  (PerfectField.separable_iff_squarefree (K := F) (g := W.preΨ n)).symm

/-- **Squarefreeness over a characteristic-zero field, in derivative form.** -/
theorem squarefree_iff_aeval_derivative_ne_zero {F : Type*} [Field F] [CharZero F]
    (p : F[X]) :
    Squarefree p ↔
      ∀ x : AlgebraicClosure F, aeval x p = 0 → aeval x (derivative p) ≠ 0 := by
  rw [← PerfectField.separable_iff_squarefree, separable_iff_aeval_derivative_ne_zero]

/-- The target in Squarefree form. -/
def S1420GenericOddPreΨSquarefree : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (W : WeierstrassCurve F) [W.IsElliptic] (n : ℤ),
    ¬ Even n → n ≠ 0 → Squarefree (W.preΨ n)

/-- **The Squarefree form is exactly the target** in characteristic zero. -/
theorem s1420_generic_iff_squarefree :
    S1366GenericOddPreΨSeparableInput ↔ S1420GenericOddPreΨSquarefree := by
  constructor
  · intro h F _ _ W _ n hodd hn
    exact (s1420_squarefree_iff_separable W n).mpr (h F W n hodd hn)
  · intro h F _ _ W _ n hodd hn
    exact (s1420_squarefree_iff_separable W n).mp (h F W n hodd hn)

/-! ## 3. The exact first algebraic lemma, in pointwise derivative form -/

/-- **The exact first algebraic lemma of the derivative route.**  For every elliptic
curve over a characteristic-zero field and every odd nonzero integer `n`, the derivative
of `preΨₙ` does not vanish at any root of `preΨₙ` (in the algebraic closure).

Equivalently (and this is proved below): `preΨₙ` has no multiple root, `preΨₙ` is
squarefree, and `gcd(preΨₙ, preΨₙ') = 1`.  None of these is assumed or reproved here;
the point of the definition is that it is the *weakest* statement in the route that is
still equivalent to the target. -/
def S1420PrePsiDerivativeNonvanishing : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (W : WeierstrassCurve F) [W.IsElliptic] (n : ℤ),
    ¬ Even n → n ≠ 0 →
      ∀ x : AlgebraicClosure F, aeval x (W.preΨ n) = 0 →
        aeval x (derivative (W.preΨ n)) ≠ 0

/-- The derivative criterion, specialised to `preΨₙ`. -/
theorem s1420_preΨ_separable_iff_derivative {F : Type*} [Field F] [CharZero F]
    (W : WeierstrassCurve F) (n : ℤ) :
    (W.preΨ n).Separable ↔
      ∀ x : AlgebraicClosure F, aeval x (W.preΨ n) = 0 →
        aeval x (derivative (W.preΨ n)) ≠ 0 :=
  separable_iff_aeval_derivative_ne_zero (W.preΨ n)

/-- **The pointwise derivative statement is exactly the target.**  Both directions are
proved: separability gives nonvanishing of the derivative at every root (Mathlib), and
nonvanishing at every root gives `IsCoprime (preΨₙ) (preΨₙ')`, i.e. separability, by
the derivative criterion. -/
theorem s1420_nonvanishing_iff_generic :
    S1420PrePsiDerivativeNonvanishing ↔ S1366GenericOddPreΨSeparableInput := by
  constructor
  · intro h F _ _ W _ n hodd hn
    exact (s1420_preΨ_separable_iff_derivative W n).mpr (h F W n hodd hn)
  · intro h F _ _ W _ n hodd hn x hx
    exact (s1420_preΨ_separable_iff_derivative W n).mp (h F W n hodd hn) x hx

/-- Squarefreeness of `preΨₙ` in derivative form. -/
theorem s1420_preΨ_squarefree_iff_derivative {F : Type*} [Field F] [CharZero F]
    (W : WeierstrassCurve F) (n : ℤ) :
    Squarefree (W.preΨ n) ↔
      ∀ x : AlgebraicClosure F, aeval x (W.preΨ n) = 0 →
        aeval x (derivative (W.preΨ n)) ≠ 0 :=
  squarefree_iff_aeval_derivative_ne_zero (W.preΨ n)

/-- **The derivative route yields the exact root count.**  Assuming the target, the
roots of `preΨₙ` in the algebraic closure are pairwise distinct and there are
`(|n|² - 1)/2` of them, its degree.  No torsion point, no cardinality and no group law
is used here: this is a consequence of separability alone. -/
theorem s1420_aroots_nodup_and_card_of_generic
    (h : S1366GenericOddPreΨSeparableInput)
    {F : Type} [Field F] [CharZero F] (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℤ} (hodd : ¬ Even n) (hchar : (n : F) ≠ 0) :
    ((W.preΨ n).aroots (AlgebraicClosure F)).Nodup ∧
      ((W.preΨ n).aroots (AlgebraicClosure F)).card = (n.natAbs ^ 2 - 1) / 2 := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hchar (by simp)
  have hsep : (W.preΨ n).Separable := h F W n hodd hn0
  have h1 : Polynomial.Separable ((W.preΨ n).map (algebraMap F (AlgebraicClosure F))) :=
    Polynomial.Separable.map (p := W.preΨ n)
      (f := algebraMap F (AlgebraicClosure F)) hsep
  have hsplit : ((W.preΨ n).map (algebraMap F (AlgebraicClosure F))).Splits :=
    IsAlgClosed.splits _
  refine ⟨?_, ?_⟩
  · change ((W.preΨ n).map (algebraMap F (AlgebraicClosure F))).roots.Nodup
    exact Polynomial.nodup_roots h1
  · change ((W.preΨ n).map (algebraMap F (AlgebraicClosure F))).roots.card =
      (n.natAbs ^ 2 - 1) / 2
    rw [← hsplit.natDegree_eq_card_roots, Polynomial.natDegree_map, W.natDegree_preΨ hchar,
      if_neg hodd]

/-- **Consumer.**  The pointwise derivative statement feeds the S1366 consumer
`s1366GenericInput_to_concrete`: it yields the concrete separability input
`S1366PreΨSeparableInput l` for every `l : PrimeGeFive`. -/
theorem s1420_concreteSeparable_of_nonvanishing
    (h : S1420PrePsiDerivativeNonvanishing) (l : PrimeGeFive) :
    S1366PreΨSeparableInput l :=
  s1366GenericInput_to_concrete (s1420_nonvanishing_iff_generic.mp h) l

/-! ## 4. Unconditional derivative facts for `preΨ` -/

/-- For odd `n`, `ΨSqₙ = preΨₙ²`. -/
theorem s1420_ΨSq_eq_preΨ_sq {R : Type*} [CommRing R] (W : WeierstrassCurve R) {n : ℤ}
    (hodd : ¬ Even n) : W.ΨSq n = W.preΨ n ^ 2 := by
  simp [WeierstrassCurve.ΨSq, if_neg hodd]

/-- **The derivative formula for odd `n`**: since `ΨSqₙ = preΨₙ²`, the derivative of
`ΨSqₙ` is `2 · preΨₙ · preΨₙ'`.  This is the only relation between the derivative of
`preΨₙ` and the division-polynomial data that Mathlib v4.32.2 provides, and it holds
over every commutative ring. -/
theorem s1420_derivative_ΨSq_eq {R : Type*} [CommRing R] (W : WeierstrassCurve R) {n : ℤ}
    (hodd : ¬ Even n) :
    derivative (W.ΨSq n) = 2 * W.preΨ n * derivative (W.preΨ n) := by
  have h : W.ΨSq n = W.preΨ n * W.preΨ n := by
    rw [s1420_ΨSq_eq_preΨ_sq W hodd, pow_two]
  rw [h, derivative_mul]
  ring

/-- **The derivative of `preΨₙ` is nonzero** for odd `n` with `(n : F) ≠ 0` and
`|n| > 2`: the degree `(|n|² - 1)/2` is at least one, so the formal derivative cannot
vanish.  This is the first necessary condition for `gcd(preΨₙ, preΨₙ') = 1` that *is*
available unconditionally. -/
theorem s1420_derivative_preΨ_ne_zero {F : Type*} [Field F] [CharZero F]
    (W : WeierstrassCurve F) {n : ℤ} (hchar : (n : F) ≠ 0) (h2 : 2 < n.natAbs) :
    derivative (W.preΨ n) ≠ 0 := by
  rw [Polynomial.derivative_ne_zero]
  exact (W.natDegree_preΨ_pos h2 hchar).ne'

/-- The pointwise derivative statement at `n = 1`: `preΨ₁ = 1` has no roots. -/
theorem s1420_nonvanishing_one (F : Type*) [Field F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic] :
    ∀ x : AlgebraicClosure F, aeval x (W.preΨ 1) = 0 →
      aeval x (derivative (W.preΨ 1)) ≠ 0 := by
  intro x hx
  simp at hx

/-- The pointwise derivative statement at `n = -1`: `preΨ₋₁ = -1` has no roots. -/
theorem s1420_nonvanishing_neg_one (F : Type*) [Field F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic] :
    ∀ x : AlgebraicClosure F, aeval x (W.preΨ (-1)) = 0 →
      aeval x (derivative (W.preΨ (-1))) ≠ 0 := by
  intro x hx
  simp at hx

/-! ## 5. Axiom footprint -/

#print axioms separable_iff_aeval_derivative_ne_zero
#print axioms s1420_generic_iff_isCoprime
#print axioms s1420_generic_iff_bezout
#print axioms s1420_squarefree_iff_separable
#print axioms s1420_generic_iff_squarefree
#print axioms s1420_preΨ_separable_iff_derivative
#print axioms s1420_nonvanishing_iff_generic
#print axioms s1420_concreteSeparable_of_nonvanishing
#print axioms s1420_ΨSq_eq_preΨ_sq
#print axioms s1420_derivative_ΨSq_eq
#print axioms s1420_derivative_preΨ_ne_zero
#print axioms s1420_nonvanishing_one
#print axioms s1420_nonvanishing_neg_one
#print axioms isCoprime_derivative_iff_no_common_root
#print axioms squarefree_iff_aeval_derivative_ne_zero
#print axioms s1420_preΨ_squarefree_iff_derivative
#print axioms s1420_aroots_nodup_and_card_of_generic

end LeanFormal.IUT.XiFPaper.S1420PrePsiDerivativeActual
