import tmp.sheaf.xif.paper.S2481CoeffLimitActual

/-!
# S2434: the reverse map of the coefficient inverse limit inverts evaluation

Layer O.  Consumer: the S2481 coefficient comparison (the evaluation
`S2481EvalLimit` must be a multiplicative equivalence
`PsiCnsCyclotome p ~= S2481CoeffLimit p`).

## What this file does

The finite coefficient limit `S2481CoeffLimit p` is the inverse limit of the
root-of-unity groups `rootsOfUnity n (O^tri)^x`.  `S2481EvalLimit` evaluates a
cyclotome `f : Hom(Q/Z, (O^tri)^x)` at the points `1/n`, and the preceding
packages prove that

* `S2481ReverseRat L q = (L.val q.pnatDen) ^ q.num` (a candidate inverse on
  rational representatives);
* `S2481ReverseRat_add` (additivity) and `S2481ReverseRat_int_add`
  (`Z`-periodicity), hence `q |-> S2481ReverseRat L q` factors through `Q/Z`.

This file packages the resulting monoid homomorphism

  `S2481Reverse L : PsiCnsCyclotome p = Hom(Q/Z, (O^tri)^x)`

by descending the additive hom `q |-> ofMul (S2481ReverseRat L q)` through the
quotient `Q/Z = Q / zmultiples 1`, and proves the round trip

  `S2481EvalLimit (S2481Reverse L) = L`.

## Method (no fake, no sorry, no axiom)

* the hom on rational representatives is `S2481ReverseRatAddHom`, built from
  `S2481ReverseRat_add`; its kernel contains `zmultiples 1` by
  `S2481ReverseRat_int_add`;
* `S2481ReverseLift` is the quotient descent (`QuotientAddGroup.lift`) of that
  hom, and `S2481Reverse` is its multiplicative form;
* the computation on the points `1/n` is the definitional unfolding of
  `S2481Reverse` plus `QuotientAddGroup.lift_mk`, and the numeric inputs
  `((1/n).num, (1/n).pnatDen) = (1, n)` are the Mathlib lemmas
  `Rat.inv_natCast_num_of_pos` and `Rat.inv_natCast_den_of_pos`;
* the two `S2481CoeffLimit` elements are equal because their value families
  are equal and the compatibility field is a proposition
  (`S2481CoeffLimit.mk.injEq`).

Only `propext`, `Classical.choice` and `Quot.sound` occur (checked at the end).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual

namespace LeanFormal.IUT.XiFPaper.S2481CoeffLimitActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-! ## 1. The rational representatives are `Z`-periodic -/

/-- The value at `0` is the identity. -/
theorem S2481ReverseRat_zero (L : S2481CoeffLimit p) :
    S2481ReverseRat (p := p) L 0 = 1 := by
  unfold S2481ReverseRat
  simp

/-- The value at an integer is the identity: the map is `Z`-periodic at `0`. -/
theorem S2481ReverseRat_intCast (L : S2481CoeffLimit p) (z : ℤ) :
    S2481ReverseRat (p := p) L ((z : ℤ) : ℚ) = 1 := by
  have h := S2481ReverseRat_int_add (p := p) L 0 z
  simpa [S2481ReverseRat_zero (p := p) L] using h

/-! ## 2. The additive hom on rational representatives -/

/-- The rational representatives, written additively for the target:
`q |-> ofMul (S2481ReverseRat L q)`.  Additivity is `S2481ReverseRat_add`. -/
noncomputable def S2481ReverseRatAddHom (L : S2481CoeffLimit p) :
    ℚ →+ Additive ((Otri p)ˣ) where
  toFun q := Additive.ofMul (S2481ReverseRat (p := p) L q)
  map_zero' := by
    change Additive.ofMul (S2481ReverseRat (p := p) L 0) = 0
    rw [S2481ReverseRat_zero]
    rfl
  map_add' q r := by
    change Additive.ofMul (S2481ReverseRat (p := p) L (q + r)) =
      Additive.ofMul (S2481ReverseRat (p := p) L q) +
        Additive.ofMul (S2481ReverseRat (p := p) L r)
    rw [S2481ReverseRat_add]
    rfl

@[simp]
theorem S2481ReverseRatAddHom_apply (L : S2481CoeffLimit p) (q : ℚ) :
    S2481ReverseRatAddHom (p := p) L q =
      Additive.ofMul (S2481ReverseRat (p := p) L q) :=
  rfl

/-- `Z`-periodicity puts `zmultiples 1` in the kernel, so the hom descends to
`Q/Z`. -/
theorem S2481ReverseRatAddHom_ker (L : S2481CoeffLimit p) :
    AddSubgroup.zmultiples (1 : ℚ) ≤
      (S2481ReverseRatAddHom (p := p) L).ker := by
  intro x hx
  rw [AddSubgroup.mem_zmultiples_iff] at hx
  obtain ⟨z, rfl⟩ := hx
  rw [AddMonoidHom.mem_ker]
  change Additive.ofMul (S2481ReverseRat (p := p) L (z • (1 : ℚ))) = 0
  rw [show (z • (1 : ℚ)) = ((z : ℤ) : ℚ) by simp,
    S2481ReverseRat_intCast (p := p) L z]
  rfl

/-! ## 3. Descent to `Q/Z` and the reverse cyclotome -/

/-- The reverse map on the rational circle `Q/Z = AddCircle 1`. -/
noncomputable def S2481ReverseLift (L : S2481CoeffLimit p) :
    AddCircle (1 : ℚ) →+ Additive ((Otri p)ˣ) :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℚ))
    (S2481ReverseRatAddHom (p := p) L)
    (S2481ReverseRatAddHom_ker (p := p) L)

/-- **The candidate inverse cyclotome** `S2481Reverse L : Hom(Q/Z, (O^tri)^x)`.
On the rational point `q` it takes the value `S2481ReverseRat L q`. -/
noncomputable def S2481Reverse (L : S2481CoeffLimit p) : PsiCnsCyclotome p where
  toFun x := Additive.toMul (S2481ReverseLift (p := p) L x.toAdd)
  map_one' := by
    change Additive.toMul
      (S2481ReverseLift (p := p) L (0 : AddCircle (1 : ℚ))) = 1
    rw [map_zero, toMul_zero]
  map_mul' x y := by
    change Additive.toMul
        (S2481ReverseLift (p := p) L (x.toAdd + y.toAdd)) =
      Additive.toMul (S2481ReverseLift (p := p) L x.toAdd) *
        Additive.toMul (S2481ReverseLift (p := p) L y.toAdd)
    rw [map_add, toMul_add]

@[simp]
theorem S2481Reverse_apply (L : S2481CoeffLimit p)
    (x : Multiplicative (AddCircle (1 : ℚ))) :
    S2481Reverse (p := p) L x =
      Additive.toMul (S2481ReverseLift (p := p) L x.toAdd) :=
  rfl

/-- On rational points the reverse cyclotome is exactly `S2481ReverseRat`. -/
theorem S2481Reverse_ofAdd_rat (L : S2481CoeffLimit p) (q : ℚ) :
    S2481Reverse (p := p) L
        (Multiplicative.ofAdd ((q : ℚ) : AddCircle (1 : ℚ))) =
      S2481ReverseRat (p := p) L q := by
  rw [S2481Reverse_apply]
  change Additive.toMul
      (S2481ReverseLift (p := p) L ((q : ℚ) : AddCircle (1 : ℚ))) =
    S2481ReverseRat (p := p) L q
  unfold S2481ReverseLift
  rw [QuotientAddGroup.lift_mk]
  rfl

/-! ## 4. The defining points `1/n` -/

/-- `(1/n).num = 1`. -/
theorem S2481_num_one_div (n : ℕ+) :
    ((1 : ℚ) / (n : ℚ)).num = 1 := by
  rw [one_div]
  exact Rat.inv_natCast_num_of_pos n.pos

/-- `(1/n).pnatDen = n`, i.e. `1/n` is in lowest terms. -/
theorem S2481_pnatDen_one_div (n : ℕ+) :
    ((1 : ℚ) / (n : ℚ)).pnatDen = n := by
  rw [Rat.pnatDen_eq_iff_den_eq, one_div, Rat.inv_natCast_den_of_pos n.pos]

/-- The reverse cyclotome recovers the `n`-th coefficient of `L` at `1/n`. -/
theorem S2481Reverse_eval_one_div (L : S2481CoeffLimit p) (n : ℕ+) :
    S2481Reverse (p := p) L
        (Multiplicative.ofAdd (((1 : ℚ) / (n : ℚ) : ℚ) : AddCircle (1 : ℚ))) =
      (((L.val n : S2481Roots p (n : ℕ)) : (Otri p)ˣ)) := by
  rw [S2481Reverse_ofAdd_rat]
  unfold S2481ReverseRat
  rw [S2481_pnatDen_one_div, S2481_num_one_div]
  exact zpow_one _

/-! ## 5. The round trip `S2481EvalLimit (S2481Reverse L) = L` -/

/-- Two coefficient-limit elements with the same value family are equal: the
compatibility field is a proposition. -/
theorem S2481CoeffLimit_eq_of_val_eq {L M : S2481CoeffLimit p}
    (h : L.val = M.val) : L = M := by
  obtain ⟨val, compat⟩ := L
  obtain ⟨val', compat'⟩ := M
  simp only at h
  subst h
  exact congrArg (fun c => (⟨val, c⟩ : S2481CoeffLimit p))
    (Subsingleton.elim compat compat')

/-- The evaluation of the reverse cyclotome returns the coefficient family. -/
theorem S2481EvalLimit_reverse_val (L : S2481CoeffLimit p) :
    (S2481EvalLimit (p := p) (S2481Reverse (p := p) L)).val = L.val := by
  funext n
  apply Subtype.ext
  show S2481Reverse (p := p) L
      (Multiplicative.ofAdd (((1 : ℚ) / (n : ℚ) : ℚ) : AddCircle (1 : ℚ))) =
    (((L.val n : S2481Roots p (n : ℕ)) : (Otri p)ˣ))
  exact S2481Reverse_eval_one_div (p := p) L n

/-- **Task C.**  The evaluation map of the coefficient limit inverts the
reverse map: `S2481EvalLimit (S2481Reverse L) = L` for every compatible
coefficient family `L`. -/
theorem S2481EvalLimit_reverse (L : S2481CoeffLimit p) :
    S2481EvalLimit (p := p) (S2481Reverse (p := p) L) = L :=
  S2481CoeffLimit_eq_of_val_eq (p := p)
    (S2481EvalLimit_reverse_val (p := p) L)

/-! ## 6. Audit trail -/

#print axioms S2481ReverseRat_zero
#print axioms S2481ReverseRat_intCast
#print axioms S2481ReverseRatAddHom_ker
#print axioms S2481Reverse_ofAdd_rat
#print axioms S2481Reverse_eval_one_div
#print axioms S2481EvalLimit_reverse

#check S2481Reverse
#check S2481EvalLimit_reverse

end LeanFormal.IUT.XiFPaper.S2481CoeffLimitActual
end
