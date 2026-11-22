import tmp.sheaf.xif.paper.S2579Kummer613Actual
import tmp.sheaf.xif.paper.S2005FprimeGroupActual

/-!
# S2581: primitivity of the actual candidate theta = a * y + i

The candidate of S2579 is `theta = S2579Theta`, whose image in
`F' = S1720Field = SplittingField (S1687H * (X^2+1))` is

  `S2579Candidate = 463856467968 * y + i`,

where `y = S1720Lift S1687Y` is a root of the S1687 sextic `S1687H` and
`i = S2579I` is an actual square root of `-1`.

This file proves

  `S2581_primitive : S2579Primitive`,

i.e. `Q(theta) = F'`, without any hypothesis, sorry or axiom.

## Argument

1. `S2581_adjoin_Y_eq_top`: the sextic `S1687H` is irreducible over Q, so
   `Q(S1687Y) = S1687Field`.  The proof does not use a general irreducibility
   criterion: if `Q(y)` had degree `3`, then `y` would lie in
   `Q(alpha)` with `alpha = y^2`; writing `y = q(alpha)` gives
   `alpha = q(alpha)^2`, so the minimal polynomial of `alpha` divides
   `X - q^2`.  Evaluating at a negative real root of the cubic `S1687P`
   (obtained by the intermediate value theorem) gives a negative real number
   equal to a square, a contradiction.

2. `S2581_E_eq_adjoin_Y`: consequently the copy `S2005E = S1720Lift.fieldRange`
   of `S1687Field` inside `F'` equals `Q(y)`.

3. `S2581_stabilizer_trivial`: no nontrivial Q-automorphism of `F'` fixes
   `theta`.  If `sigma(theta) = theta`, then either `sigma(i) = i`, in which
   case `sigma` fixes `Q(y)` and `i`, hence fixes all of
   `F' = Q(y) + Q(i)`; or `sigma(i) = -i`, in which case
   `a (sigma(y) - y) = 2 i` puts `i` in `Q(y)`, contradicting
   `S2005_no_sqrt_neg_one_in_E`.

4. Galois correspondence (`IsGalois.fixedField_fixingSubgroup`): the fixing
   subgroup of `Q(theta)` is trivial, so `Q(theta)` is the whole field.

## Reused verified facts

The proof reuses the following already-verified results:

* from S1993: `S1993Pmonic`, `S1993Pmonic_monic`,
  `S1993Pmonic_irreducible` and `S1993Pmonic_natDegree`;
* from S1999: `S1999S1687Field_finrank : [S1687Field : Q] = 6`;
* from S2005: `S2005_roots_H_mem_E`, `S2005_no_sqrt_neg_one_in_E`,
  `S2005I_sq`, `S2005E_sup_adjoin_I_eq_top` and the identification of
  `S2005E` with the image of the sextic field.

The external sympy facts about the minimal polynomial of the candidate (degree
twelve and irreducibility of `S2579P12`) are **not** used: primitivity is
proved by the Galois-theoretic argument above.  The remaining inputs of the
S2579 Kummer-Dedekind step, `S2579Conductor613` and `S2579LinearFactor613`,
are untouched here.

No axiom, sorry, `True`, `native_decide` or opaque declaration is used.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

open Polynomial
open scoped IntermediateField

namespace LeanFormal.IUT.XiFPaper.S2581PrimitiveThetaActual

open LeanFormal.IUT.XiFPaper.S2579Kummer613Actual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S2005FprimeGroupActual
open LeanFormal.IUT.XiFPaper.S1993D5FiniteGroupBridgeActual
open LeanFormal.IUT.XiFPaper.S1999S1993BridgeActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual

/-! ## 1. The square of the S1687 root has degree three -/

/-- The minimal polynomial of `S1687Y ^ 2` is the monicisation of `S1687P`. -/
theorem S2581Alpha_minpoly :
    minpoly ℚ (S1687Y ^ 2) = S1993Pmonic := by
  have hp : aeval (S1687Y ^ 2) S1993Pmonic = 0 := by
    rw [S1993Pmonic, map_mul, S1687Y_sq_root, zero_mul]
  exact (minpoly.eq_of_irreducible_of_monic (A := ℚ) (B := S1687Field)
    (x := S1687Y ^ 2) (p := S1993Pmonic)
    S1993Pmonic_irreducible hp S1993Pmonic_monic).symm

/-- `[Q(S1687Y^2) : Q] = 3`. -/
theorem S2581Alpha_finrank :
    Module.finrank ℚ (ℚ⟮S1687Y ^ 2⟯ : IntermediateField ℚ S1687Field) = 3 := by
  rw [IntermediateField.adjoin.finrank (IsIntegral.of_finite ℚ (S1687Y ^ 2)),
    S2581Alpha_minpoly, S1993Pmonic_natDegree]

/-! ## 2. The cubic `S1687P` has a negative real root -/

/-- The cubic `S1687P` has a strictly negative real root. -/
theorem S2581_realRoot : ∃ ρ : ℝ, aeval ρ S1687P = 0 ∧ ρ < 0 := by
  have hcont : Continuous fun t : ℝ => aeval t S1687P := S1687P.continuous_aeval
  have hneg : aeval (-10 : ℝ) S1687P < 0 := by
    unfold S1687P
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C]
    norm_num
  have hpos : (0 : ℝ) < aeval (0 : ℝ) S1687P := by
    unfold S1687P
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C]
    norm_num
  have hmem : (0 : ℝ) ∈ Set.Icc (aeval (-10 : ℝ) S1687P) (aeval (0 : ℝ) S1687P) :=
    Set.mem_Icc.mpr ⟨le_of_lt hneg, le_of_lt hpos⟩
  obtain ⟨ρ, hρI, hρ0⟩ :=
    (intermediate_value_Icc (show (-10 : ℝ) ≤ 0 by norm_num) hcont.continuousOn) hmem
  refine ⟨ρ, hρ0, ?_⟩
  rcases lt_or_eq_of_le hρI.2 with h | h
  · exact h
  · exfalso
    have hz : aeval (0 : ℝ) S1687P = 0 := by simpa [h] using hρ0
    linarith

/-! ## 3. `S1687Y` is not in `Q(S1687Y^2)`, hence generates the sextic field -/

/-- `S1687Y` does not lie in the cubic subfield generated by its square. -/
theorem S2581_not_mem_adjoin_sq
    (hY : S1687Y ∈ (ℚ⟮S1687Y ^ 2⟯ : IntermediateField ℚ S1687Field)) : False := by
  have hYalg : IsAlgebraic ℚ (S1687Y ^ 2) :=
    (IsIntegral.of_finite ℚ (S1687Y ^ 2)).isAlgebraic
  have hY' : S1687Y ∈ Algebra.adjoin ℚ ({S1687Y ^ 2} : Set S1687Field) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (F := ℚ)
      (E := S1687Field) (α := S1687Y ^ 2) hYalg]
    exact hY
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hY'
  obtain ⟨q, hq⟩ := hY'
  have hq' : aeval (S1687Y ^ 2) q = S1687Y := by simpa using hq
  have h0 : aeval (S1687Y ^ 2) (X - q * q) = 0 := by
    simp only [map_sub, map_mul, aeval_X]
    rw [hq']
    ring
  have hdvd : minpoly ℚ (S1687Y ^ 2) ∣ (X - q * q) :=
    minpoly.dvd ℚ (S1687Y ^ 2) h0
  obtain ⟨s, hs⟩ := hdvd
  obtain ⟨ρ, hρroot, hρneg⟩ := S2581_realRoot
  have hmin : aeval ρ (minpoly ℚ (S1687Y ^ 2)) = 0 := by
    rw [S2581Alpha_minpoly, S1993Pmonic, map_mul, hρroot, zero_mul]
  have hρ : ρ = (aeval ρ q) ^ 2 := by
    have h := congrArg (fun p : ℚ[X] => aeval ρ p) hs
    simp only [map_sub, map_mul, aeval_X] at h
    rw [hmin, zero_mul] at h
    have h' : ρ - aeval ρ q * aeval ρ q = 0 := h
    rw [pow_two]
    linarith
  nlinarith [sq_nonneg (aeval ρ q)]

/-- `S1687Y` generates the splitting field `S1687Field` over Q. -/
theorem S2581_adjoin_Y_eq_top :
    (ℚ⟮S1687Y⟯ : IntermediateField ℚ S1687Field) = ⊤ := by
  set f := Module.finrank ℚ (ℚ⟮S1687Y⟯ : IntermediateField ℚ S1687Field) with hf
  have hle : (ℚ⟮S1687Y ^ 2⟯ : IntermediateField ℚ S1687Field) ≤ ℚ⟮S1687Y⟯ := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ S1687Y) 2
  have hdvd3 : 3 ∣ f := by
    rw [hf, ← S2581Alpha_finrank]
    exact IntermediateField.finrank_dvd_of_le_right hle
  have hdvd6 : f ∣ 6 := by
    rw [hf]
    have h := IntermediateField.finrank_dvd_of_le_right (K := ℚ)
      (F := (ℚ⟮S1687Y⟯ : IntermediateField ℚ S1687Field))
      (E := (⊤ : IntermediateField ℚ S1687Field)) le_top
    rwa [IntermediateField.finrank_top', S1999S1687Field_finrank] at h
  have hne3 : f ≠ 3 := by
    intro h3
    have heq : (ℚ⟮S1687Y ^ 2⟯ : IntermediateField ℚ S1687Field) = ℚ⟮S1687Y⟯ := by
      refine IntermediateField.eq_of_le_of_finrank_eq hle ?_
      rw [S2581Alpha_finrank, ← hf]
      exact h3.symm
    exact S2581_not_mem_adjoin_sq (by
      rw [heq]
      exact IntermediateField.mem_adjoin_simple_self ℚ S1687Y)
  have h6 : f = 6 := by
    obtain ⟨k, hk⟩ := hdvd3
    obtain ⟨l, hl⟩ := hdvd6
    have hkl : k * l = 2 := by
      have h6' : 6 = 3 * (k * l) := by
        rw [hk, mul_assoc] at hl
        exact hl
      have h32 : (6 : ℕ) = 3 * 2 := by norm_num
      rw [h32] at h6'
      exact (Nat.mul_left_cancel (by norm_num : 0 < 3) h6').symm
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · rw [h0, zero_mul] at hkl
        norm_num at hkl
      · exact hpos
    have hk2 : k ∣ 2 := ⟨l, by rw [hkl]⟩
    have hkle : k ≤ 2 := Nat.le_of_dvd (by norm_num) hk2
    interval_cases k
    · exfalso
      exact hne3 (by simpa using hk)
    · simpa using hk
  have htop : f = Module.finrank ℚ (⊤ : IntermediateField ℚ S1687Field) := by
    rw [IntermediateField.finrank_top', h6, S1999S1687Field_finrank]
  exact IntermediateField.eq_of_le_of_finrank_eq le_top (by rw [← hf]; exact htop)

/-! ## 4. The copy of the sextic field inside F' is Q(y) -/

/-- `S2005E = Q(S1720Lift S1687Y)` inside `F'`. -/
theorem S2581_E_eq_adjoin_Y :
    S2005E = (ℚ⟮S2579Y⟯ : IntermediateField ℚ S1720Field) := by
  have hmap := IntermediateField.adjoin_map (F := ℚ)
    (S := ({S1687Y} : Set S1687Field)) S1720Lift
  rw [S2581_adjoin_Y_eq_top, Set.image_singleton] at hmap
  rw [← AlgHom.fieldRange_eq_map] at hmap
  simpa [S2579Y, S2005E] using hmap

/-! ## 5. The two square roots of -1 -/

/-- The S2579 choice of square root of -1 differs from the S2005 choice by a sign. -/
theorem S2581I_eq_or_neg : S2579I = S2005I ∨ S2579I = -S2005I := by
  have hsq : (S2579I - S2005I) * (S2579I + S2005I) = 0 := by
    have h1 : S2579I * S2579I = (-1 : S1720Field) := S2579I_sq
    have h2 : S2005I * S2005I = (-1 : S1720Field) := by rw [← sq]; exact S2005I_sq
    linear_combination h1 - h2
  rcases mul_eq_zero.mp hsq with h | h
  · left
    linear_combination h
  · right
    linear_combination h

/-! ## 6. The stabilizer of theta is trivial -/

/-- No nontrivial Q-automorphism of `F'` fixes `theta = a*y + i`. -/
theorem S2581_stabilizer_trivial (σ : S1720Field ≃ₐ[ℚ] S1720Field)
    (hθ : σ S2579Candidate = S2579Candidate) : σ = 1 := by
  have hkey : (463856467968 : S1720Field) * (σ S2579Y - S2579Y) =
      S2579I - σ S2579I := by
    have h := hθ
    unfold S2579Candidate at h
    rw [map_add, map_mul] at h
    have hnum : (S2579a : S1720Field) = (463856467968 : S1720Field) := by
      norm_num [S2579a]
    rw [hnum] at h
    have ha : (463856467968 : S1720Field) =
        algebraMap ℚ S1720Field (463856467968 : ℚ) := by norm_num
    have hσa : σ (463856467968 : S1720Field) = (463856467968 : S1720Field) := by
      rw [ha, AlgEquiv.commutes]
    rw [hσa] at h
    linear_combination h
  have hIsq : (σ S2579I) ^ 2 = (-1 : S1720Field) := by
    rw [← map_pow, sq, S2579I_sq, map_neg, map_one]
  have hIcase : σ S2579I = S2579I ∨ σ S2579I = -S2579I := by
    have hprod : (σ S2579I - S2579I) * (σ S2579I + S2579I) = 0 := by
      have h1 : S2579I * S2579I = (-1 : S1720Field) := S2579I_sq
      have h2 : σ S2579I * σ S2579I = (-1 : S1720Field) := by
        rw [← sq]; exact hIsq
      linear_combination h2 - h1
    rcases mul_eq_zero.mp hprod with h | h
    · left; linear_combination h
    · right; linear_combination h
  rcases hIcase with hσI | hσI
  · -- sigma fixes the chosen square root of -1
    have hσ2005 : σ S2005I = S2005I := by
      rcases S2581I_eq_or_neg with h | h
      · rw [← h]; exact hσI
      · have h2 : σ (-S2005I) = -S2005I := by rw [← h]; exact hσI
        have h3 : -(σ S2005I) = -S2005I := by simpa using h2
        exact neg_injective h3
    have hy : σ S2579Y = S2579Y := by
      have h0 : (463856467968 : S1720Field) * (σ S2579Y - S2579Y) = 0 := by
        rw [hkey, hσI]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left (by norm_num))
    have hy_stab : σ ∈ MulAction.stabilizer (S1720Field ≃ₐ[ℚ] S1720Field) S2579Y := by
      rw [MulAction.mem_stabilizer_iff]
      simpa [AlgEquiv.smul_def] using hy
    have hI_stab : σ ∈ MulAction.stabilizer (S1720Field ≃ₐ[ℚ] S1720Field) S2005I := by
      rw [MulAction.mem_stabilizer_iff]
      simpa [AlgEquiv.smul_def] using hσ2005
    have hfixE : S2005E ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [S2581_E_eq_adjoin_Y, IntermediateField.adjoin_le_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      change S2579Y ∈ IntermediateField.fixedField (Subgroup.zpowers σ)
      rw [IntermediateField.mem_fixedField_iff]
      intro f hf
      exact MulAction.mem_stabilizer_iff.mp (Subgroup.zpowers_le.mpr hy_stab hf)
    have hfixI : (ℚ⟮S2005I⟯ : IntermediateField ℚ S1720Field) ≤
        IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      change S2005I ∈ IntermediateField.fixedField (Subgroup.zpowers σ)
      rw [IntermediateField.mem_fixedField_iff]
      intro f hf
      exact MulAction.mem_stabilizer_iff.mp (Subgroup.zpowers_le.mpr hI_stab hf)
    have htop : IntermediateField.fixedField (Subgroup.zpowers σ) = ⊤ := by
      refine le_antisymm le_top ?_
      rw [← S2005E_sup_adjoin_I_eq_top]
      exact sup_le hfixE hfixI
    refine AlgEquiv.ext fun x => ?_
    have hx : x ∈ IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [htop]; exact trivial
    have hfix : σ x = x :=
      (IntermediateField.mem_fixedField_iff (Subgroup.zpowers σ) x).mp hx σ (Subgroup.mem_zpowers σ)
    simpa using hfix
  · -- sigma sends i to -i: then i would lie in Q(y)
    exfalso
    have h2 : (463856467968 : S1720Field) * (σ S2579Y - S2579Y) = 2 * S2579I := by
      rw [hkey, hσI]; ring
    have hσyE : σ S2579Y ∈ S2005E := by
      apply S2005_roots_H_mem_E
      rw [Polynomial.mem_rootSet_of_ne S1687H_ne_zero]
      have h := Polynomial.aeval_algHom_apply σ S2579Y S1687H
      rw [S2579Y_root, map_zero] at h
      exact h
    have hyE : S2579Y ∈ S2005E := by
      rw [show S2579Y = S1720Lift S1687Y from rfl]
      exact AlgHom.mem_fieldRange.mpr ⟨S1687Y, rfl⟩
    have haE : (463856467968 : S1720Field) ∈ S2005E := by
      have h : (463856467968 : S1720Field) =
          algebraMap ℚ S1720Field (463856467968 : ℚ) := by norm_num
      rw [h]
      exact IntermediateField.algebraMap_mem S2005E _
    have hprodE : (463856467968 : S1720Field) * (σ S2579Y - S2579Y) ∈ S2005E :=
      mul_mem haE (sub_mem hσyE hyE)
    rw [h2] at hprodE
    have h2E : (2 : S1720Field) ∈ S2005E := by
      have h : (2 : S1720Field) = algebraMap ℚ S1720Field (2 : ℚ) := by norm_num
      rw [h]
      exact IntermediateField.algebraMap_mem S2005E _
    have hIE : S2579I ∈ S2005E := by
      have hdiv : (2 * S2579I) / 2 ∈ S2005E := div_mem hprodE h2E
      convert hdiv using 1
      field_simp
    exact S2005_no_sqrt_neg_one_in_E hIE (by rw [sq]; exact S2579I_sq)

/-! ## 7. The fixing subgroup of Q(theta) is trivial, so Q(theta) = F' -/

/-- The primitive element statement for the actual candidate. -/
theorem S2581_primitive : S2579Primitive := by
  unfold S2579Primitive
  rw [S2579Theta_coe]
  have hfix : IntermediateField.fixingSubgroup
      (ℚ⟮S2579Candidate⟯ : IntermediateField ℚ S1720Field) = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    have hθ : σ S2579Candidate = S2579Candidate :=
      (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ S2579Candidate
        (IntermediateField.mem_adjoin_simple_self ℚ S2579Candidate)
    exact S2581_stabilizer_trivial σ hθ
  calc (ℚ⟮S2579Candidate⟯ : IntermediateField ℚ S1720Field)
      = IntermediateField.fixedField (IntermediateField.fixingSubgroup
          (ℚ⟮S2579Candidate⟯ : IntermediateField ℚ S1720Field)) :=
        (IsGalois.fixedField_fixingSubgroup _).symm
    _ = IntermediateField.fixedField (⊥ : Subgroup (S1720Field ≃ₐ[ℚ] S1720Field)) := by
        rw [hfix]
    _ = ⊤ := IntermediateField.fixedField_bot

/-! ## 8. Consumer form and axiom footprint -/

/-- The consumer form of the Kummer-Dedekind step of S2579: primitivity is no
longer an input, only the conductor condition and the linear residue factor
remain. -/
theorem S2581_prime613_of_conductor_linear
    (hc : S2579Conductor613) (hl : S2579LinearFactor613) :
    ∃ P : Ideal S, P.IsPrime ∧ P.LiesOver (Ideal.span {(613 : ℤ)}) ∧
      Nonempty (S ⧸ P ≃+* ZMod 613) :=
  S2579_prime613_of_arithmetic hc hl

#print axioms S2581Alpha_minpoly
#print axioms S2581Alpha_finrank
#print axioms S2581_realRoot
#print axioms S2581_not_mem_adjoin_sq
#print axioms S2581_adjoin_Y_eq_top
#print axioms S2581_E_eq_adjoin_Y
#print axioms S2581I_eq_or_neg
#print axioms S2581_stabilizer_trivial
#print axioms S2581_primitive
#print axioms S2581_prime613_of_conductor_linear

end LeanFormal.IUT.XiFPaper.S2581PrimitiveThetaActual
end
