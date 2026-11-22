import tmp.sheaf.xif.paper.S2000CohomologicalPsiCnsActual
import tmp.sheaf.xif.paper.S2431IndexEqActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
namespace LeanFormal.IUT.XiFPaper.S2481CoeffLimitActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- The finite root-of-unity groups in the actual integral monoid. -/
abbrev S2481Roots (n : ℕ) : Subgroup (Otri p)ˣ :=
  rootsOfUnity n (Otri p)

/-- Projection of the inverse system, by raising to the quotient exponent. -/
noncomputable def S2481Proj {m n : ℕ} (h : m ∣ n) :
    S2481Roots p n →* S2481Roots p m where
  toFun ζ := ⟨(ζ : (Otri p)ˣ) ^ (n / m), by
    rw [mem_rootsOfUnity]
    have hζ := (mem_rootsOfUnity n (ζ : (Otri p)ˣ)).mp ζ.2
    calc
      (((ζ : (Otri p)ˣ) ^ (n / m)) ^ m) =
          (ζ : (Otri p)ˣ) ^ ((n / m) * m) := by rw [pow_mul]
      _ = (ζ : (Otri p)ˣ) ^ n := by rw [Nat.div_mul_cancel h]
      _ = 1 := hζ⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_pow]

/-- The inverse-limit carrier of finite roots of unity. -/
structure S2481CoeffLimit where
  val : (n : ℕ+) → S2481Roots p (n : ℕ)
  compat : ∀ (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ)),
    S2481Proj p h (val n) = val m


/-- Evaluation of a cyclotome hom at the point 1/n, giving a finite root of
unity. -/
noncomputable def S2481Eval (f : PsiCnsCyclotome p) (n : ℕ+) :
    S2481Roots p (n : ℕ) :=
  ⟨f (Multiplicative.ofAdd (((1 : ℚ) / (n : ℚ) : ℚ) : AddCircle (1 : ℚ))), by
    rw [mem_rootsOfUnity]
    rw [← map_pow]
    have hx : (n : ℕ) • (((1 : ℚ) / (n : ℚ) : ℚ) : AddCircle (1 : ℚ)) = 0 := by
      rw [← AddCircle.coe_nsmul]
      rw [nsmul_eq_mul]
      rw [show (n : ℚ) * ((1 : ℚ) / (n : ℚ)) = 1 by
        field_simp]
      simp
    have hpow : (Multiplicative.ofAdd
        (((1 : ℚ) / (n : ℚ) : ℚ) : AddCircle (1 : ℚ))) ^ (n : ℕ) = 1 := by
      rw [← ofAdd_nsmul]
      rw [hx, ofAdd_zero]
    rw [hpow, map_one]⟩



/-- Projection compatibility of the evaluation map. -/
theorem S2481Eval_compat (f : PsiCnsCyclotome p)
    {m n : ℕ+} (h : (m : ℕ) ∣ (n : ℕ)) :
    S2481Proj p h (S2481Eval p f n) = S2481Eval p f m := by
  apply Subtype.ext
  change (f (Multiplicative.ofAdd
      (((1 : ℚ) / (n : ℚ) : ℚ) : AddCircle (1 : ℚ)))) ^
      ((n : ℕ) / (m : ℕ)) =
    f (Multiplicative.ofAdd
      (((1 : ℚ) / (m : ℚ) : ℚ) : AddCircle (1 : ℚ)))
  rw [← map_pow, ← ofAdd_nsmul]
  congr 1
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
  have hmq : ((m : ℕ) : ℚ) ≠ 0 := by exact_mod_cast m.ne_zero
  have hnq : ((n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hdiv : ((((n : ℕ) / (m : ℕ)) : ℕ) : ℚ) =
      ((n : ℚ) / (m : ℚ)) := by
    rw [Nat.cast_div h] <;> exact hmq
  have hq : ((((n : ℕ) / (m : ℕ)) : ℕ) : ℚ) *
      ((1 : ℚ) / (n : ℚ)) = (1 : ℚ) / (m : ℚ) := by
    rw [hdiv]
    field_simp [hmq, hnq] <;> assumption
  rw [hq]


/-- Packaging the compatible evaluation family as an element of the inverse
limit. -/
noncomputable def S2481EvalLimit (f : PsiCnsCyclotome p) :
    S2481CoeffLimit p where
  val n := S2481Eval p f n
  compat m n h := S2481Eval_compat p f h


/-- Each value has the expected finite order. -/
theorem S2481_val_pow (L : S2481CoeffLimit p) (n : ℕ+) :
    ((L.val n : S2481Roots p (n : ℕ)) : (Otri p)ˣ) ^ (n : ℕ) = 1 :=
  (mem_rootsOfUnity (n : ℕ) ((L.val n : S2481Roots p (n : ℕ)) : (Otri p)ˣ)).mp
    (L.val n).2

/-- Compatibility in power form: the m-value is the (n/m)-power of the
n-value when m ∣ n. -/
theorem S2481_val_eq_pow (L : S2481CoeffLimit p)
    {m n : ℕ+} (h : (m : ℕ) ∣ (n : ℕ)) :
    ((L.val m : S2481Roots p (m : ℕ)) : (Otri p)ˣ) =
      (((L.val n : S2481Roots p (n : ℕ)) : (Otri p)ˣ) ^
        ((n : ℕ) / (m : ℕ))) := by
  have hc := congrArg (fun x : S2481Roots p (m : ℕ) => (x : (Otri p)ˣ))
    (L.compat m n h).symm
  simpa [S2481Proj] using hc



/-- Core exponent-independence for the reverse map. -/
theorem S2481_coe_independent (L : S2481CoeffLimit p)
    {k k' : ℤ} {m n : ℕ+}
    (h : Int.ModEq ((n : ℤ) * (m : ℤ)) ((m : ℤ) * k) ((n : ℤ) * k')) :
    (((L.val n : S2481Roots p (n : ℕ)) : (Otri p)ˣ) ^ k) =
      (((L.val m : S2481Roots p (m : ℕ)) : (Otri p)ˣ) ^ k') := by
  let N : ℕ+ := n * m
  let u : (Otri p)ˣ := (L.val N : S2481Roots p (N : ℕ))
  have hmN : (m : ℕ) ∣ (N : ℕ) := ⟨n, by dsimp [N]; rw [mul_comm]⟩
  have hnN : (n : ℕ) ∣ (N : ℕ) := ⟨m, rfl⟩
  have hn := S2481_val_eq_pow (p := p) L hnN
  have hm := S2481_val_eq_pow (p := p) L hmN
  rw [hn, hm]
  have hdivn : (N : ℕ) / (n : ℕ) = (m : ℕ) := by
    dsimp [N]; rw [mul_comm]; exact Nat.mul_div_left _ n.pos
  have hdivm : (N : ℕ) / (m : ℕ) = (n : ℕ) := by
    dsimp [N]; exact Nat.mul_div_left _ m.pos
  rw [hdivn, hdivm]
  change (u ^ ((m : ℕ) : ℤ)) ^ k = (u ^ ((n : ℕ) : ℤ)) ^ k'
  rw [← zpow_mul, ← zpow_mul]
  apply zpow_eq_zpow_iff_modEq.mpr
  have huN : u ^ (N : ℕ) = 1 := by
    simpa [u, N] using S2481_val_pow (p := p) L N
  have hord : (orderOf u : ℤ) ∣ (N : ℤ) := by
    rw [orderOf_dvd_iff_zpow_eq_one]
    simpa [zpow_natCast] using huN
  have hNcast : ((N : ℕ) : ℤ) = (n : ℤ) * (m : ℤ) := by
    dsimp [N]
  have hmod : Int.ModEq ((N : ℕ) : ℤ) ((m : ℤ) * k) ((n : ℤ) * k') := by
    simpa [hNcast] using h
  exact Int.modEq_iff_dvd.mpr
    (dvd_trans hord (Int.modEq_iff_dvd.mp hmod))


/-- Candidate inverse on rational representatives: q ↦ (val q.pnatDen)^q.num. -/
noncomputable def S2481ReverseRat (L : S2481CoeffLimit p) (q : ℚ) : (Otri p)ˣ :=
  ((L.val q.pnatDen : S2481Roots p (q.pnatDen : ℕ)) : (Otri p)ˣ) ^ q.num


theorem S2481_pnatDen_add_one (q : ℚ) :
    (q + 1).pnatDen = q.pnatDen := by
  rw [Rat.pnatDen_eq_iff_den_eq, Rat.coe_pnatDen]
  exact Rat.add_natCast_den q 1

theorem S2481_num_add_one (q : ℚ) :
    (q + 1).num = q.num + (q.den : ℤ) := by
  have h := Rat.add_num_den' q 1
  have hden : (q + 1).den = q.den := Rat.add_natCast_den q 1
  rw [hden] at h
  have hq : ((q.den : ℤ)) ≠ 0 := by exact_mod_cast q.den_ne_zero
  apply mul_right_cancel₀ hq
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

theorem S2481ReverseRat_add_one (L : S2481CoeffLimit p) (q : ℚ) :
    S2481ReverseRat (p := p) L (q + 1) = S2481ReverseRat (p := p) L q := by
  unfold S2481ReverseRat
  rw [S2481_pnatDen_add_one, S2481_num_add_one]
  rw [zpow_add]
  have h := S2481_val_pow (p := p) L q.pnatDen
  have h' : ((L.val q.pnatDen : S2481Roots p (q.pnatDen : ℕ)) : (Otri p)ˣ) ^ (q.den : ℤ) = 1 := by
    simpa [Rat.coe_pnatDen] using h
  rw [h', mul_one]


theorem S2481ReverseRat_sub_one (L : S2481CoeffLimit p) (q : ℚ) :
    S2481ReverseRat (p := p) L (q - 1) = S2481ReverseRat (p := p) L q := by
  simpa using (S2481ReverseRat_add_one (p := p) L (q - 1)).symm



theorem S2481ReverseRat_int_add (L : S2481CoeffLimit p) (q : ℚ) (z : ℤ) :
    S2481ReverseRat (p := p) L (q + (z : ℚ)) = S2481ReverseRat (p := p) L q := by
  revert q
  refine Int.inductionOn'
    (motive := fun z => ∀ q : ℚ,
      S2481ReverseRat (p := p) L (q + (z : ℚ)) = S2481ReverseRat (p := p) L q)
    z 0 ?_ ?_ ?_
  · intro q
    simp
  · intro k hk ih q
    have hcast : (((k + 1 : ℤ) : ℚ) = (k : ℚ) + 1) := by
      push_cast
      ring
    have h : q + ((k : ℚ) + 1) = (q + (k : ℚ)) + 1 := by ring
    rw [hcast, h, S2481ReverseRat_add_one, ih]
  · intro k hk ih q
    have hcast : (((k - 1 : ℤ) : ℚ) = (k : ℚ) - 1) := by
      push_cast
      ring
    have h : q + ((k : ℚ) - 1) = (q + (k : ℚ)) - 1 := by ring
    rw [hcast, h, S2481ReverseRat_sub_one, ih]


theorem S2481ReverseRat_eq_pow (L : S2481CoeffLimit p) (q : ℚ) (N : ℕ+)
    (h : (q.pnatDen : ℕ) ∣ (N : ℕ)) :
    S2481ReverseRat (p := p) L q =
      ((L.val N : S2481Roots p (N : ℕ)) : (Otri p)ˣ) ^
        ((((N : ℕ) / (q.pnatDen : ℕ) : ℕ) : ℤ) * q.num) := by
  unfold S2481ReverseRat
  rw [S2481_val_eq_pow (p := p) L h]
  rw [← zpow_natCast]
  rw [← zpow_mul]


theorem S2481_pnatDen_add_dvd (q r : ℚ) :
    (q + r).pnatDen ∣ q.pnatDen * r.pnatDen := by
  have hnat : ((q + r).pnatDen : ℕ) ∣
      ((q.pnatDen : ℕ) * (r.pnatDen : ℕ)) := by
    simpa [Rat.coe_pnatDen] using Rat.add_den_dvd q r
  exact PNat.dvd_iff.mpr hnat


theorem S2481ReverseRat_add (L : S2481CoeffLimit p) (q r : ℚ) :
    S2481ReverseRat (p := p) L (q + r) =
      S2481ReverseRat (p := p) L q * S2481ReverseRat (p := p) L r := by
  let N : ℕ+ := q.pnatDen * r.pnatDen
  have hq : (q.pnatDen : ℕ) ∣ (N : ℕ) := by
    dsimp [N]; exact dvd_mul_right _ _
  have hr : (r.pnatDen : ℕ) ∣ (N : ℕ) := by
    dsimp [N]; exact dvd_mul_left _ _
  have hqr : ((q + r).pnatDen : ℕ) ∣ (N : ℕ) := by
    dsimp [N]
    simpa [Rat.coe_pnatDen] using Rat.add_den_dvd q r
  rw [S2481ReverseRat_eq_pow (p := p) L q N hq,
    S2481ReverseRat_eq_pow (p := p) L r N hr,
    S2481ReverseRat_eq_pow (p := p) L (q + r) N hqr]
  rw [← zpow_add]
  congr 1
  simpa [N] using S2481_index_eq q r

#check S2481Roots
#check S2481ReverseRat_add
#check S2481_pnatDen_add_dvd
#check S2481ReverseRat_eq_pow
#check S2481ReverseRat_int_add
#check S2481ReverseRat_add_one
#check S2481ReverseRat
#check S2481_coe_independent
#check S2481_val_pow
#check S2481_val_eq_pow
#check S2481EvalLimit
#check S2481Eval_compat
#check S2481Eval
#check S2481Proj
#check S2481CoeffLimit

end LeanFormal.IUT.XiFPaper.S2481CoeffLimitActual
end