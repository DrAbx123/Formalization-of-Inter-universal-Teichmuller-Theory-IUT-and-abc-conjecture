import tmp.sheaf.xif.paper.S2481CoeffLimitActual

/-!
# S2432: the reverse map from the coefficient limit to the cyclotome

Given `L : S2481CoeffLimit p`, the rational candidate
`S2481ReverseRat L : ℚ → (Otri p)ˣ` satisfies the additivity law
`S2481ReverseRat_add` and is invariant under adding integers
(`S2481ReverseRat_int_add`).  Hence it kills the subgroup
`zmultiples (1 : ℚ) ⊆ ℚ` and therefore descends through the quotient
`ℚ → ℚ ⧸ ℤ = AddCircle 1` to a group homomorphism

  `S2481Reverse L : Multiplicative (AddCircle (1 : ℚ)) →* (Otri p)ˣ`,

which is definitionally the cyclotome `PsiCnsCyclotome p` of S2000.
The evaluation formula `S2481Reverse_apply` records that this hom is the
descended rational map, and `S2481Reverse_type` records the identification
of its type with the task's hom-type.
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

/-- The rational candidate is trivial at `0`. -/
theorem S2481ReverseRat_zero (L : S2481CoeffLimit p) :
    S2481ReverseRat (p := p) L 0 = 1 := by
  simp [S2481ReverseRat]

/-- The rational candidate is trivial at `1`; this is the integer translation
that is needed for the quotient by `ℤ`. -/
theorem S2481ReverseRat_one (L : S2481CoeffLimit p) :
    S2481ReverseRat (p := p) L 1 = 1 := by
  have h := S2481ReverseRat_int_add (p := p) L 0 1
  have h' : S2481ReverseRat (p := p) L 1 = S2481ReverseRat (p := p) L 0 := by
    simpa using h
  rw [h', S2481ReverseRat_zero]

/-- The rational candidate, viewed as an additive character with values in the
additively written unit group. -/
noncomputable def S2481ReverseRatAddHom (L : S2481CoeffLimit p) :
    ℚ →+ Additive (Otri p)ˣ where
  toFun q := Additive.ofMul (S2481ReverseRat (p := p) L q)
  map_zero' := congrArg Additive.ofMul (S2481ReverseRat_zero (p := p) L)
  map_add' q r := congrArg Additive.ofMul (S2481ReverseRat_add (p := p) L q r)

/-- The integer lattice lies in the kernel of the rational candidate. -/
theorem S2481ReverseRat_zmultiples_le (L : S2481CoeffLimit p) :
    AddSubgroup.zmultiples (1 : ℚ) ≤ (S2481ReverseRatAddHom (p := p) L).ker := by
  rw [AddSubgroup.zmultiples_le]
  change S2481ReverseRatAddHom (p := p) L 1 = 0
  apply Additive.toMul.injective
  exact S2481ReverseRat_one (p := p) L

/-- **Task A**: the reverse map, obtained by descending the rational candidate
through the quotient `ℚ → ℚ ⧸ ℤ`.  Its codomain is definitionally
`Multiplicative (AddCircle (1 : ℚ)) →* (Otri p)ˣ`, i.e. `PsiCnsCyclotome p`. -/
noncomputable def S2481Reverse (L : S2481CoeffLimit p) : PsiCnsCyclotome p :=
  AddMonoidHom.toMultiplicativeLeft
    (QuotientAddGroup.lift
      (AddSubgroup.zmultiples (1 : ℚ))
      (S2481ReverseRatAddHom (p := p) L)
      (S2481ReverseRat_zmultiples_le (p := p) L))

/-- Evaluation of the reverse map on a rational representative. -/
@[simp] theorem S2481Reverse_apply (L : S2481CoeffLimit p) (q : ℚ) :
    S2481Reverse (p := p) L (Multiplicative.ofAdd (q : AddCircle (1 : ℚ))) =
      S2481ReverseRat (p := p) L q := rfl

/-- The constructed reverse map literally has the hom-type recorded in the
task statement. -/
theorem S2481Reverse_type :
    PsiCnsCyclotome p =
      (Multiplicative (AddCircle (1 : ℚ)) →* (Otri p)ˣ) := rfl

end LeanFormal.IUT.XiFPaper.S2481CoeffLimitActual

#print axioms LeanFormal.IUT.XiFPaper.S2481CoeffLimitActual.S2481Reverse
#print axioms LeanFormal.IUT.XiFPaper.S2481CoeffLimitActual.S2481Reverse_apply
#print axioms LeanFormal.IUT.XiFPaper.S2481CoeffLimitActual.S2481ReverseRat_zmultiples_le
#print axioms LeanFormal.IUT.XiFPaper.S2481CoeffLimitActual.S2481ReverseRat_one
