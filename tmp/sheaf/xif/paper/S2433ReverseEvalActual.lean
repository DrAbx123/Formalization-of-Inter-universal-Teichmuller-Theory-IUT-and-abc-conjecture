import tmp.sheaf.xif.paper.S2481CoeffLimitActual
import tmp.sheaf.xif.paper.S2046G1CyclotomeActual

/-!
# S2433: the reverse evaluation map and the round trip with `S2481EvalLimit`

Given a compatible family `L` of roots of unity, the reverse map sends a class
`q : ℚ/ℤ` to `(L.val q.den) ^ q.num`.  Additivity (`S2481ReverseRat_add`) and
periodicity (`S2481ReverseRat_int_add`) make it a homomorphism
`Multiplicative (AddCircle 1) →* (Otri p)ˣ`, i.e. an element of
`PsiCnsCyclotome p`.  This file constructs that homomorphism and proves

  `S2481Reverse (S2481EvalLimit f) = f`.

The reverse map itself was not available in `S2481CoeffLimitActual.lean`, so it
is constructed here from the actual ingredients proved there; no inverse is
assumed and no well-definedness is postulated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2046G1CyclotomeActual
namespace LeanFormal.IUT.XiFPaper.S2481CoeffLimitActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-! ## Auxiliary values of the reverse map at integers -/

theorem S2481ReverseRat_one (L : S2481CoeffLimit p) :
    S2481ReverseRat (p := p) L 1 = 1 := by
  unfold S2481ReverseRat
  rw [Rat.pnatDen_one, Rat.num_one]
  simpa using S2481_val_pow (p := p) L 1

theorem S2481ReverseRat_zero (L : S2481CoeffLimit p) :
    S2481ReverseRat (p := p) L 0 = 1 := by
  unfold S2481ReverseRat
  rw [Rat.pnatDen_zero, Rat.num_zero]
  simp

theorem S2481ReverseRat_int (L : S2481CoeffLimit p) (z : ℤ) :
    S2481ReverseRat (p := p) L (z : ℚ) = 1 := by
  have h := S2481ReverseRat_int_add (p := p) L 0 z
  simpa [S2481ReverseRat_zero (p := p) L] using h

/-! ## The additive hom on rational representatives -/

noncomputable def S2481ReverseRatAddHom (L : S2481CoeffLimit p) :
    ℚ →+ Additive (Otri p)ˣ where
  toFun q := Additive.ofMul (S2481ReverseRat (p := p) L q)
  map_zero' := by
    simp [S2481ReverseRat_zero]
  map_add' q r := by
    simp [S2481ReverseRat_add]

theorem S2481_zmultiples_le_ker (L : S2481CoeffLimit p) :
    AddSubgroup.zmultiples (1 : ℚ) ≤ (S2481ReverseRatAddHom (p := p) L).ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker]
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  rw [map_zsmul]
  simp [S2481ReverseRatAddHom, S2481ReverseRat_one]

/-! ## Descent to the circle and the reverse map -/

noncomputable def S2481ReverseAdd (L : S2481CoeffLimit p) :
    AddCircle (1 : ℚ) →+ Additive (Otri p)ˣ :=
  QuotientAddGroup.lift (N := AddSubgroup.zmultiples (1 : ℚ))
    (φ := S2481ReverseRatAddHom (p := p) L)
    (S2481_zmultiples_le_ker (p := p) L)

noncomputable def S2481Reverse (L : S2481CoeffLimit p) : PsiCnsCyclotome p where
  toFun x := Additive.toMul (S2481ReverseAdd (p := p) L (Multiplicative.toAdd x))
  map_one' := by
    simp [S2481ReverseAdd]
  map_mul' x y := by
    simp [S2481ReverseAdd, toAdd_mul]

theorem S2481Reverse_ofAdd (L : S2481CoeffLimit p) (q : ℚ) :
    S2481Reverse (p := p) L
        (Multiplicative.ofAdd ((q : ℚ) : AddCircle (1 : ℚ))) =
      S2481ReverseRat (p := p) L q := by
  show Additive.toMul
      (S2481ReverseAdd (p := p) L ((q : ℚ) : AddCircle (1 : ℚ))) =
    S2481ReverseRat (p := p) L q
  unfold S2481ReverseAdd
  rw [QuotientAddGroup.lift_mk]
  rfl

/-! ## Evaluation of the reverse map on a limit built from a cyclotome -/

theorem S2481ReverseRat_EvalLimit (f : PsiCnsCyclotome p) (q : ℚ) :
    S2481ReverseRat (p := p) (S2481EvalLimit (p := p) f) q =
      f (Multiplicative.ofAdd ((q : ℚ) : AddCircle (1 : ℚ))) := by
  unfold S2481ReverseRat
  have hbase : ((S2481EvalLimit (p := p) f).val q.pnatDen : (Otri p)ˣ) =
      f (Multiplicative.ofAdd
        (((1 : ℚ) / ((q.pnatDen : ℕ) : ℚ) : ℚ) : AddCircle (1 : ℚ))) := rfl
  rw [hbase]
  rw [← map_zpow, ← ofAdd_zsmul, ← AddCircle.coe_zsmul]
  have hq : q.num • ((1 : ℚ) / ((q.pnatDen : ℕ) : ℚ)) = q := by
    have hd : ((q.pnatDen : ℕ) : ℚ) = (q.den : ℚ) := by
      rw [Rat.coe_pnatDen]
    calc q.num • ((1 : ℚ) / ((q.pnatDen : ℕ) : ℚ))
        = (q.num : ℚ) * (1 / (q.den : ℚ)) := by rw [hd, zsmul_eq_mul]
      _ = (q.num : ℚ) / (q.den : ℚ) := by ring
      _ = q := Rat.num_div_den q
  rw [hq]

/-! ## The round trip -/

theorem S2481Reverse_EvalLimit (f : PsiCnsCyclotome p) :
    S2481Reverse (p := p) (S2481EvalLimit (p := p) f) = f := by
  apply MonoidHom.ext
  intro x
  obtain ⟨q, hq⟩ := Quotient.mk_surjective x.toAdd
  have hx : x = Multiplicative.ofAdd ((q : ℚ) : AddCircle (1 : ℚ)) := by
    calc x = Multiplicative.ofAdd x.toAdd := (ofAdd_toAdd x).symm
      _ = Multiplicative.ofAdd ((q : ℚ) : AddCircle (1 : ℚ)) := by rw [← hq]
  rw [hx, S2481Reverse_ofAdd, S2481ReverseRat_EvalLimit]

theorem S2481Reverse_EvalLimit_apply (f : PsiCnsCyclotome p)
    (x : Multiplicative (AddCircle (1 : ℚ))) :
    S2481Reverse (p := p) (S2481EvalLimit (p := p) f) x = f x := by
  rw [S2481Reverse_EvalLimit]

/-! ## The reverse evaluation round trip -/

theorem S2481_num_one_div (n : ℕ+) :
    ((1 : ℚ) / (n : ℚ)).num = 1 := by
  rw [one_div]
  exact Rat.inv_natCast_num_of_pos n.pos

theorem S2481_pnatDen_one_div (n : ℕ+) :
    ((1 : ℚ) / (n : ℚ)).pnatDen = n := by
  rw [Rat.pnatDen_eq_iff_den_eq, one_div, Rat.inv_natCast_den_of_pos n.pos]

theorem S2481CoeffLimit_eq_of_val_eq {L M : S2481CoeffLimit p}
    (h : L.val = M.val) : L = M := by
  obtain ⟨val, compat⟩ := L
  obtain ⟨val', compat'⟩ := M
  simp only at h
  subst h
  exact congrArg (fun c => (⟨val, c⟩ : S2481CoeffLimit p))
    (Subsingleton.elim compat compat')

theorem S2481EvalLimit_reverse_val (L : S2481CoeffLimit p) :
    (S2481EvalLimit (p := p) (S2481Reverse (p := p) L)).val = L.val := by
  funext n
  apply Subtype.ext
  show S2481Reverse (p := p) L
      (Multiplicative.ofAdd (((1 : ℚ) / (n : ℚ) : ℚ) : AddCircle (1 : ℚ))) =
    (((L.val n : S2481Roots p (n : ℕ)) : (Otri p)ˣ))
  rw [S2481Reverse_ofAdd]
  unfold S2481ReverseRat
  rw [S2481_pnatDen_one_div, S2481_num_one_div]
  exact zpow_one _

theorem S2481EvalLimit_reverse (L : S2481CoeffLimit p) :
    S2481EvalLimit (p := p) (S2481Reverse (p := p) L) = L :=
  S2481CoeffLimit_eq_of_val_eq (p := p)
    (S2481EvalLimit_reverse_val (p := p) L)


/-- Bijection between the actual cyclotome and the finite root-of-unity
inverse limit. -/
noncomputable def S2481Equiv : PsiCnsCyclotome p ≃ S2481CoeffLimit p where
  toFun := S2481EvalLimit (p := p)
  invFun := S2481Reverse (p := p)
  left_inv := S2481Reverse_EvalLimit (p := p)
  right_inv := S2481EvalLimit_reverse (p := p)



instance : One (S2481CoeffLimit p) where
  one :=
    { val := fun _ => 1
      compat := by
        intro m n h
        rw [map_one] }

instance : Mul (S2481CoeffLimit p) where
  mul L M :=
    { val := fun n => L.val n * M.val n
      compat := by
        intro m n h
        change (S2481Proj p h) (L.val n * M.val n) = L.val m * M.val m
        rw [map_mul, L.compat m n h, M.compat m n h] }

instance : Inv (S2481CoeffLimit p) where
  inv L :=
    { val := fun n => (L.val n)⁻¹
      compat := by
        intro m n h
        change (S2481Proj p h) ((L.val n)⁻¹) = (L.val m)⁻¹
        rw [map_inv, L.compat m n h] }


theorem S2481CoeffLimit_ext {L M : S2481CoeffLimit p}
    (h : L.val = M.val) : L = M := by
  cases L with
  | mk val compat =>
    cases M with
    | mk val' compat' =>
      simp only at h
      subst h
      exact congrArg (fun c => (⟨val, c⟩ : S2481CoeffLimit p))
        (Subsingleton.elim compat compat')

instance : Monoid (S2481CoeffLimit p) where
  one_mul L := by
    apply S2481CoeffLimit_ext
    funext n
    exact one_mul (L.val n)
  mul_one L := by
    apply S2481CoeffLimit_ext
    funext n
    exact mul_one (L.val n)
  mul_assoc L M N := by
    apply S2481CoeffLimit_ext
    funext n
    exact mul_assoc (L.val n) (M.val n) (N.val n)

instance : Group (S2481CoeffLimit p) :=
  Group.ofLeftAxioms
    (fun L M N => mul_assoc L M N)
    (fun L => one_mul L)
    (fun L => by
      apply S2481CoeffLimit_ext
      funext n
      exact inv_mul_cancel (L.val n))


theorem S2481EvalLimit_mul (f g : PsiCnsCyclotome p) :
    S2481EvalLimit (p := p) (f * g) =
      S2481EvalLimit (p := p) f * S2481EvalLimit (p := p) g := by
  apply S2481CoeffLimit_eq_of_val_eq (p := p)
  funext n
  apply Subtype.ext
  rfl

noncomputable def S2481MulEquiv :
    PsiCnsCyclotome p ≃* S2481CoeffLimit p where
  toFun := S2481EvalLimit (p := p)
  invFun := S2481Reverse (p := p)
  left_inv := S2481Reverse_EvalLimit (p := p)
  right_inv := S2481EvalLimit_reverse (p := p)
  map_mul' := S2481EvalLimit_mul (p := p)

/-! ## Topological structure -/

/-- Transport the cyclotome topology across the coefficient equivalence. -/
instance S2481CoeffLimit_topologicalSpace :
    TopologicalSpace (S2481CoeffLimit p) :=
  (S2481MulEquiv (p := p)).toEquiv.symm.topologicalSpace



noncomputable def S2481Action : Gv p →* MulAut (S2481CoeffLimit p) where
  toFun g :=
    { toFun := fun L =>
        S2481MulEquiv (p := p) (S2046G1PsiCnsAction p g ((S2481MulEquiv (p := p)).symm L))
      invFun := fun L =>
        S2481MulEquiv (p := p) (S2046G1PsiCnsAction p g⁻¹ ((S2481MulEquiv (p := p)).symm L))
      left_inv := by
        intro L
        simp
      right_inv := by
        intro L
        simp
      map_mul' := by
        intro L M
        simp [map_mul] }
  map_one' := by
    ext L
    simp
  map_mul' g h := by
    ext L
    simp [MulAut.mul_apply, map_mul]




noncomputable def S2481Homeomorph : PsiCnsCyclotome p ≃ₜ S2481CoeffLimit p :=
  (Equiv.homeomorph (S2481MulEquiv (p := p)).toEquiv.symm).symm

@[simp] theorem S2481Homeomorph_toEquiv :
    (S2481Homeomorph (p := p)).toEquiv =
      (S2481MulEquiv (p := p)).toEquiv :=
  rfl

@[simp] theorem S2481Homeomorph_apply (x : PsiCnsCyclotome p) :
    S2481Homeomorph (p := p) x = S2481MulEquiv (p := p) x :=
  rfl

@[simp] theorem S2481Homeomorph_symm_apply (x : S2481CoeffLimit p) :
    (S2481Homeomorph (p := p)).symm x = (S2481MulEquiv (p := p)).symm x :=
  rfl

instance S2481CoeffLimit_isTopologicalGroup :
    IsTopologicalGroup (S2481CoeffLimit p) where
  continuous_mul := by
    have hsrc : Continuous
        (fun q : PsiCnsCyclotome p × PsiCnsCyclotome p => q.1 * q.2) :=
      continuous_mul
    have hpair : Continuous
        (fun q : S2481CoeffLimit p × S2481CoeffLimit p =>
          ((S2481Homeomorph (p := p)).symm q.1,
            (S2481Homeomorph (p := p)).symm q.2)) :=
      ((S2481Homeomorph (p := p)).symm.continuous.comp continuous_fst).prodMk
        (((S2481Homeomorph (p := p)).symm.continuous.comp continuous_snd))
    have h := (S2481Homeomorph (p := p)).continuous.comp (hsrc.comp hpair)
    convert h using 1
    ext q
    simp [S2481Homeomorph_apply, S2481Homeomorph_symm_apply, map_mul]
  continuous_inv := by
    have hsrc : Continuous (fun x : PsiCnsCyclotome p => x⁻¹) := continuous_inv
    have h := (S2481Homeomorph (p := p)).continuous.comp
      (hsrc.comp (S2481Homeomorph (p := p)).symm.continuous)
    convert h using 1
    ext q
    simp [S2481Homeomorph_apply, S2481Homeomorph_symm_apply, map_inv]





theorem S2481Action_continuous :
    Continuous (fun q : Gv p × S2481CoeffLimit p =>
      S2481Action (p := p) q.1 q.2) := by
  have hsource : Continuous (fun q : Gv p × PsiCnsCyclotome p =>
      (PsiCnsCoefficientAction p).automorphism q.1 q.2) :=
    (PsiCnsCoefficientAction p).continuous_action
  have hlift : Continuous (fun q : Gv p × S2481CoeffLimit p =>
      (q.1, S2481Homeomorph (p := p).symm q.2)) :=
    continuous_fst.prodMk
      (S2481Homeomorph (p := p).symm.continuous.comp continuous_snd)
  have hhome := S2481Homeomorph (p := p).continuous.comp (hsource.comp hlift)
  have hact : (fun q : Gv p × S2481CoeffLimit p =>
      S2481Action (p := p) q.1 q.2) =
    (fun q : Gv p × S2481CoeffLimit p =>
      S2481Homeomorph (p := p) (
        ((PsiCnsCoefficientAction p).automorphism q.1)
          (S2481Homeomorph (p := p).symm q.2))) := by
    funext q
    simp [S2481Action, S2481Homeomorph_apply, S2481Homeomorph_symm_apply]
  rw [hact]
  exact hhome


noncomputable def S2481ContinuousAction :
    Iut.ContinuousGroupAction (Gv p) (S2481CoeffLimit p) where
  automorphism := S2481Action (p := p)
  continuous_action := S2481Action_continuous (p := p)

end LeanFormal.IUT.XiFPaper.S2481CoeffLimitActual
end