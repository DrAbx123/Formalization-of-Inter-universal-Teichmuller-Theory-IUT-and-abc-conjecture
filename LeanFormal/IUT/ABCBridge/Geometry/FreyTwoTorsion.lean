import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import LeanFormal.IUT.ABCBridge.Geometry.FreyWeierstrassCurve
import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation

/-!
# Rational two-torsion of the Frey Weierstrass model

The Frey model of this project is the actual Mathlib `WeierstrassCurve`
`y ^ 2 = x * (x - a) * (x + b)` from `FreyWeierstrassCurve.lean`.  This file
studies its actual `2`-torsion using Mathlib's affine point group law and the
proved `two`-division-polynomial evaluation interface of
`EllipticDivisionPolynomialEvaluation.lean`.

The nontrivial rational `2`-torsion is identified with the three displayed
cubic roots `0`, `a`, `-b`: each point `(r, 0)` is on the curve exactly when
`x * (x - a) * (x + b)` vanishes at `r`, each such point is killed by `2`,
they are pairwise distinct exactly under the ellipticity hypotheses, and every
`2`-torsion point of the elliptic curve is `0` or one of the three.  The
`2`-torsion subgroup is exactly the closure of `{(0,0), (a,0), (-b,0)}` and
has four elements.

Consumer: the Frey-to-Legendre comparison chain, whose exhibited variable
change transports the branch coordinates `0`, `1`, `a / c` of the Legendre
model to the Frey branch coordinates `a`, `-b`, `0`; this file supplies the
Frey side of that ordered branch data.  No odd-`l` theory, no descent, and no
integrality claims are made here.
-/

noncomputable section

namespace LeanFormal.IUT

open WeierstrassCurve

universe u

section RingRoots

variable {R : Type u} [CommRing R]

/-- The three displayed roots `0`, `a`, `-b` of the Frey cubic, as an ordered
triple.  The ordering is the one read off from the factorized right-hand side
`x * (x - a) * (x + b)`. -/
def freyTwoTorsionRoots (a b : R) : Fin 3 → R := ![0, a, -b]

@[simp] theorem freyTwoTorsionRoots_zero (a b : R) :
    freyTwoTorsionRoots a b 0 = 0 := rfl

@[simp] theorem freyTwoTorsionRoots_one (a b : R) :
    freyTwoTorsionRoots a b 1 = a := rfl

@[simp] theorem freyTwoTorsionRoots_two (a b : R) :
    freyTwoTorsionRoots a b 2 = -b := rfl

/-- The displayed cubic is the product over the ordered root triple. -/
theorem freyTwoTorsionRoots_factorization (a b x : R) :
    x * (x - a) * (x + b) = ∏ i : Fin 3, (x - freyTwoTorsionRoots a b i) := by
  rw [Fin.prod_univ_three]
  simp only [freyTwoTorsionRoots_zero, freyTwoTorsionRoots_one, freyTwoTorsionRoots_two]
  ring

/-- The affine Frey equation with zero `y`-coordinate is exactly the vanishing
of the displayed cubic.  The only input is the actual equation lemma
`freyWeierstrassCurve_equation`. -/
theorem freyWeierstrassCurve_equation_y_zero_iff (a b x : R) :
    (freyWeierstrassCurve a b).toAffine.Equation x 0 ↔ x * (x - a) * (x + b) = 0 := by
  rw [WeierstrassCurve.Affine.equation_iff, freyWeierstrassCurve_equation a b x 0]
  simp only [zero_pow (by decide : (2 : Nat) ≠ 0)]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- The actual Mathlib two-torsion polynomial of the Frey model is four times
the displayed cubic. -/
theorem freyWeierstrassCurve_twoTorsionPolynomial (a b : R) :
    (freyWeierstrassCurve a b).twoTorsionPolynomial = ⟨4, 4 * (b - a), -4 * (a * b), 0⟩ := by
  apply Cubic.ext
  · rfl
  · simp only [WeierstrassCurve.twoTorsionPolynomial, freyWeierstrassCurve_b₂]
  · simp only [WeierstrassCurve.twoTorsionPolynomial, freyWeierstrassCurve_b₄]
    ring
  · simp only [WeierstrassCurve.twoTorsionPolynomial, freyWeierstrassCurve_b₆]

/-- The discriminant of the actual two-torsion polynomial is sixteen times the
actual Frey discriminant, displayed on the additive parameters. -/
theorem freyWeierstrassCurve_twoTorsionPolynomial_discr (a b : R) :
    (freyWeierstrassCurve a b).twoTorsionPolynomial.discr = 256 * (a * b * (a + b)) ^ 2 := by
  rw [WeierstrassCurve.twoTorsionPolynomial_discr, freyWeierstrassCurve_discriminant]
  ring

end RingRoots

section FieldRoots

variable {K : Type u} [Field K]

/-- The roots of the displayed cubic, as the exact `x`-coordinates of the
zero-`y` solutions of the affine equation. -/
theorem freyWeierstrassCurve_equation_y_zero_iff_roots (a b x : K) :
    (freyWeierstrassCurve a b).toAffine.Equation x 0 ↔ x = 0 ∨ x = a ∨ x = -b := by
  rw [freyWeierstrassCurve_equation_y_zero_iff a b x]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hleft | hb
    · rcases mul_eq_zero.mp hleft with hx | ha
      · exact Or.inl hx
      · exact Or.inr (Or.inl (sub_eq_zero.mp ha))
    · exact Or.inr (Or.inr (add_eq_zero_iff_eq_neg.mp hb))
  · rintro (rfl | rfl | rfl) <;> ring

end FieldRoots

section ParameterExtraction

variable {K : Type u} [Field K] (a b : K)

/-- Ellipticity of the Frey model forces characteristic different from two. -/
theorem freyWeierstrassCurve_two_ne_zero_of_isElliptic
    (hE : (freyWeierstrassCurve a b).IsElliptic) : (2 : K) ≠ 0 := by
  intro htwo
  have hdiscriminant : (freyWeierstrassCurve a b).Δ ≠ 0 := hE.isUnit.ne_zero
  apply hdiscriminant
  rw [freyWeierstrassCurve_discriminant]
  have hsixteen : (16 : K) = 0 := by
    rw [show (16 : K) = 2 ^ 4 by norm_num, htwo]
    norm_num
  rw [hsixteen]
  ring

/-- The ellipticity of the Frey model is exactly the nonvanishing of `a`, `b`,
and `a + b`, with characteristic different from two; here the three
parameter conditions are extracted. -/
theorem freyWeierstrassCurve_parameters_of_isElliptic
    (hE : (freyWeierstrassCurve a b).IsElliptic) :
    a ≠ 0 ∧ b ≠ 0 ∧ a + b ≠ 0 := by
  have htwo := freyWeierstrassCurve_two_ne_zero_of_isElliptic a b hE
  have h := (freyWeierstrassCurve_isElliptic_iff a b).mp hE
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

end ParameterExtraction

section TorsionPoints

variable {K : Type u} [Field K] (a b : K) [(freyWeierstrassCurve a b).IsElliptic]

/-- The affine point `(0, 0)` of the Frey model. -/
def freyTwoTorsionPointRootZero : (freyWeierstrassCurve a b).toAffine.Point :=
  WeierstrassCurve.Affine.Point.some 0 0
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((freyWeierstrassCurve_equation_y_zero_iff a b 0).mpr (by ring)))

/-- The affine point `(a, 0)` of the Frey model. -/
def freyTwoTorsionPointRootA : (freyWeierstrassCurve a b).toAffine.Point :=
  WeierstrassCurve.Affine.Point.some a 0
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((freyWeierstrassCurve_equation_y_zero_iff a b a).mpr (by ring)))

/-- The affine point `(-b, 0)` of the Frey model. -/
def freyTwoTorsionPointRootNegB : (freyWeierstrassCurve a b).toAffine.Point :=
  WeierstrassCurve.Affine.Point.some (-b) 0
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((freyWeierstrassCurve_equation_y_zero_iff a b (-b)).mpr (by ring)))

theorem freyTwoTorsionPointRootZero_ne_zero : freyTwoTorsionPointRootZero a b ≠ 0 :=
  fun h => WeierstrassCurve.Affine.Point.some_ne_zero (W' := (freyWeierstrassCurve a b).toAffine)
    (x := 0) (y := 0)
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((freyWeierstrassCurve_equation_y_zero_iff a b 0).mpr (by ring))) h

theorem freyTwoTorsionPointRootA_ne_zero : freyTwoTorsionPointRootA a b ≠ 0 :=
  fun h => WeierstrassCurve.Affine.Point.some_ne_zero (W' := (freyWeierstrassCurve a b).toAffine)
    (x := a) (y := 0)
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((freyWeierstrassCurve_equation_y_zero_iff a b a).mpr (by ring))) h

theorem freyTwoTorsionPointRootNegB_ne_zero : freyTwoTorsionPointRootNegB a b ≠ 0 :=
  fun h => WeierstrassCurve.Affine.Point.some_ne_zero (W' := (freyWeierstrassCurve a b).toAffine)
    (x := -b) (y := 0)
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((freyWeierstrassCurve_equation_y_zero_iff a b (-b)).mpr (by ring))) h

theorem freyTwoTorsionPointRootZero_ne_rootA :
    freyTwoTorsionPointRootZero a b ≠ freyTwoTorsionPointRootA a b := by
  intro h
  have hx : (0 : K) = a :=
    (WeierstrassCurve.Affine.Point.X_eq_iff (x₁ := 0) (y₁ := 0) (x₂ := a) (y₂ := 0)).mpr (Or.inl h)
  exact (freyWeierstrassCurve_parameters_of_isElliptic a b inferInstance).1 hx.symm

theorem freyTwoTorsionPointRootZero_ne_rootNegB :
    freyTwoTorsionPointRootZero a b ≠ freyTwoTorsionPointRootNegB a b := by
  intro h
  have hx : (0 : K) = -b :=
    (WeierstrassCurve.Affine.Point.X_eq_iff (x₁ := 0) (y₁ := 0) (x₂ := -b) (y₂ := 0)).mpr (Or.inl h)
  exact (freyWeierstrassCurve_parameters_of_isElliptic a b inferInstance).2.1
    (neg_eq_zero.mp hx.symm)

theorem freyTwoTorsionPointRootA_ne_rootNegB :
    freyTwoTorsionPointRootA a b ≠ freyTwoTorsionPointRootNegB a b := by
  intro h
  have hx : a = -b :=
    (WeierstrassCurve.Affine.Point.X_eq_iff (x₁ := a) (y₁ := 0) (x₂ := -b) (y₂ := 0)).mpr (Or.inl h)
  exact (freyWeierstrassCurve_parameters_of_isElliptic a b inferInstance).2.2 (by rw [hx]; simp)

end TorsionPoints

section TwoTorsionStructure

variable {K : Type u} [Field K] [DecidableEq K] (a b : K) [(freyWeierstrassCurve a b).IsElliptic]

theorem freyTwoTorsionPointRootZero_two_nsmul :
    (2 : Nat) • freyTwoTorsionPointRootZero a b = 0 := by
  rw [two_nsmul]
  refine WeierstrassCurve.Affine.Point.add_self_of_Y_eq ?_
  rw [← (freyWeierstrassCurve a b).evalDivisionPolynomial_two_eq_zero_iff_negY]
  simp

theorem freyTwoTorsionPointRootA_two_nsmul :
    (2 : Nat) • freyTwoTorsionPointRootA a b = 0 := by
  rw [two_nsmul]
  refine WeierstrassCurve.Affine.Point.add_self_of_Y_eq ?_
  rw [← (freyWeierstrassCurve a b).evalDivisionPolynomial_two_eq_zero_iff_negY]
  simp

theorem freyTwoTorsionPointRootNegB_two_nsmul :
    (2 : Nat) • freyTwoTorsionPointRootNegB a b = 0 := by
  rw [two_nsmul]
  refine WeierstrassCurve.Affine.Point.add_self_of_Y_eq ?_
  rw [← (freyWeierstrassCurve a b).evalDivisionPolynomial_two_eq_zero_iff_negY]
  simp

/-- Every rational `2`-torsion point of the Frey elliptic curve is the zero
point or one of the three displayed branch points. -/
theorem freyTwoTorsion_eq_zero_or_root (P : (freyWeierstrassCurve a b).toAffine.Point)
    (hP : (2 : Nat) • P = 0) :
    P = 0 ∨ P = freyTwoTorsionPointRootZero a b ∨ P = freyTwoTorsionPointRootA a b ∨
      P = freyTwoTorsionPointRootNegB a b := by
  cases P with
  | zero => exact Or.inl rfl
  | some x y h =>
    right
    have hy2 : (2 : K) * y = 0 := by
      have hpsi :=
        ((freyWeierstrassCurve a b).two_nsmul_some_eq_zero_iff_evalDivisionPolynomial_two_eq_zero
            h).mp hP
      rw [WeierstrassCurve.evalDivisionPolynomial_two] at hpsi
      simpa [freyWeierstrassCurve_a₁, freyWeierstrassCurve_a₃] using hpsi
    have hy : y = 0 := by
      rcases mul_eq_zero.mp hy2 with hzero | hyzero
      · exact absurd hzero (freyWeierstrassCurve_two_ne_zero_of_isElliptic a b inferInstance)
      · exact hyzero
    subst hy
    rcases (freyWeierstrassCurve_equation_y_zero_iff_roots a b x).mp h.1 with hx | hx | hx
    · subst hx
      exact Or.inl rfl
    · subst hx
      exact Or.inr (Or.inl rfl)
    · subst hx
      exact Or.inr (Or.inr rfl)

/-- A nonzero `2`-torsion point of the Frey curve has one of the three
displayed cubic roots as its affine `x`-coordinate. -/
theorem freyTwoTorsion_some_x_eq_roots {x y : K}
    (h : (freyWeierstrassCurve a b).toAffine.Nonsingular x y)
    (h2 : (2 : Nat) • WeierstrassCurve.Affine.Point.some x y h = 0)
    (hne : WeierstrassCurve.Affine.Point.some x y h ≠ 0) :
    x = 0 ∨ x = a ∨ x = -b := by
  rcases freyTwoTorsion_eq_zero_or_root a b _ h2 with h0 | h | h | h
  · exact absurd h0 hne
  · exact Or.inl ((WeierstrassCurve.Affine.Point.X_eq_iff (x₁ := x) (y₁ := y)
      (x₂ := 0) (y₂ := 0)).mpr (Or.inl h))
  · exact Or.inr (Or.inl ((WeierstrassCurve.Affine.Point.X_eq_iff (x₁ := x) (y₁ := y)
      (x₂ := a) (y₂ := 0)).mpr (Or.inl h)))
  · exact Or.inr (Or.inr ((WeierstrassCurve.Affine.Point.X_eq_iff (x₁ := x) (y₁ := y)
      (x₂ := -b) (y₂ := 0)).mpr (Or.inl h)))

/-- The actual rational `2`-torsion set of the Frey elliptic curve. -/
def freyTwoTorsionSet : Set (freyWeierstrassCurve a b).toAffine.Point :=
  {P | (2 : Nat) • P = 0}

/-- The four explicit points of the Frey `2`-torsion. -/
def freyTwoTorsionFinset : Finset (freyWeierstrassCurve a b).toAffine.Point :=
  {0, freyTwoTorsionPointRootZero a b, freyTwoTorsionPointRootA a b,
    freyTwoTorsionPointRootNegB a b}

theorem freyTwoTorsionSet_eq :
    freyTwoTorsionSet a b = ↑(freyTwoTorsionFinset a b) := by
  ext P
  simp only [freyTwoTorsionSet, Set.mem_setOf_eq, Finset.mem_coe, freyTwoTorsionFinset,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · exact freyTwoTorsion_eq_zero_or_root a b P
  · rintro (rfl | rfl | rfl | rfl)
    · simp
    · exact freyTwoTorsionPointRootZero_two_nsmul a b
    · exact freyTwoTorsionPointRootA_two_nsmul a b
    · exact freyTwoTorsionPointRootNegB_two_nsmul a b

theorem freyTwoTorsionFinset_card : (freyTwoTorsionFinset a b).card = 4 := by
  have hZeroNotMem : (0 : (freyWeierstrassCurve a b).toAffine.Point) ∉
      ({freyTwoTorsionPointRootZero a b, freyTwoTorsionPointRootA a b,
        freyTwoTorsionPointRootNegB a b} : Finset _) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨(freyTwoTorsionPointRootZero_ne_zero a b).symm,
      (freyTwoTorsionPointRootA_ne_zero a b).symm,
      (freyTwoTorsionPointRootNegB_ne_zero a b).symm⟩
  have hRootZeroNotMem : freyTwoTorsionPointRootZero a b ∉
      ({freyTwoTorsionPointRootA a b, freyTwoTorsionPointRootNegB a b} : Finset _) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨freyTwoTorsionPointRootZero_ne_rootA a b,
      freyTwoTorsionPointRootZero_ne_rootNegB a b⟩
  have hRootANotMem : freyTwoTorsionPointRootA a b ∉
      ({freyTwoTorsionPointRootNegB a b} : Finset _) := by
    simp only [Finset.mem_singleton]
    exact freyTwoTorsionPointRootA_ne_rootNegB a b
  rw [freyTwoTorsionFinset, Finset.card_insert_of_notMem hZeroNotMem,
    Finset.card_insert_of_notMem hRootZeroNotMem, Finset.card_insert_of_notMem hRootANotMem,
    Finset.card_singleton]

theorem freyTwoTorsionSet_ncard : (freyTwoTorsionSet a b).ncard = 4 := by
  rw [freyTwoTorsionSet_eq a b, Set.ncard_coe_finset]
  exact freyTwoTorsionFinset_card a b

/-- The `2`-torsion subgroup of the Frey elliptic curve, as an additive
subgroup of its point group. -/
def freyTwoTorsionSubgroup : AddSubgroup (freyWeierstrassCurve a b).toAffine.Point where
  carrier := freyTwoTorsionSet a b
  zero_mem' := by
    change (2 : Nat) • (0 : (freyWeierstrassCurve a b).toAffine.Point) = 0
    simp
  add_mem' := by
    intro P Q hP hQ
    change (2 : Nat) • (P + Q) = 0
    have hP' : (2 : Nat) • P = 0 := hP
    have hQ' : (2 : Nat) • Q = 0 := hQ
    rw [nsmul_add, hP', hQ', add_zero]
  neg_mem' := by
    intro P hP
    change (2 : Nat) • (-P) = 0
    have hP' : (2 : Nat) • P = 0 := hP
    rw [smul_neg, hP', neg_zero]

set_option linter.unusedSectionVars false in
theorem freyTwoTorsionSubgroup_coe :
    (↑(freyTwoTorsionSubgroup a b) : Set (freyWeierstrassCurve a b).toAffine.Point) =
      freyTwoTorsionSet a b := rfl

theorem freyTwoTorsionSubgroup_ncard :
    (↑(freyTwoTorsionSubgroup a b) : Set (freyWeierstrassCurve a b).toAffine.Point).ncard = 4 := by
  rw [freyTwoTorsionSubgroup_coe a b]
  exact freyTwoTorsionSet_ncard a b

/-- The Frey `2`-torsion subgroup is generated by the three displayed branch
points. -/
theorem freyTwoTorsionSubgroup_eq_closure :
    freyTwoTorsionSubgroup a b =
      AddSubgroup.closure ({freyTwoTorsionPointRootZero a b, freyTwoTorsionPointRootA a b,
        freyTwoTorsionPointRootNegB a b} : Set (freyWeierstrassCurve a b).toAffine.Point) := by
  apply le_antisymm
  · intro P hP
    have hP' : (2 : Nat) • P = 0 := hP
    rcases freyTwoTorsion_eq_zero_or_root a b P hP' with rfl | rfl | rfl | rfl
    · exact AddSubgroup.zero_mem _
    · exact AddSubgroup.subset_closure (by simp)
    · exact AddSubgroup.subset_closure (by simp)
    · exact AddSubgroup.subset_closure (by simp)
  · rw [AddSubgroup.closure_le]
    intro P hP
    have hP' : P = freyTwoTorsionPointRootZero a b ∨ P = freyTwoTorsionPointRootA a b ∨
        P = freyTwoTorsionPointRootNegB a b := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hP
    rcases hP' with rfl | rfl | rfl
    · exact freyTwoTorsionPointRootZero_two_nsmul a b
    · exact freyTwoTorsionPointRootA_two_nsmul a b
    · exact freyTwoTorsionPointRootNegB_two_nsmul a b

end TwoTorsionStructure

end LeanFormal.IUT
