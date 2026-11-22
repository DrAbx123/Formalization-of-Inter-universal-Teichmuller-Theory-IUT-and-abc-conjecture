/-
# B1 — the graph isomorphism of route (b) for the submersive model (P2)

Consumer: Mzk1G1B1SmoothCriterionSubmActual.GraphIso h, the single missing ingredient of
smoothAt_of_derivative_notMem (direction B of the smooth <-> derivative criterion).  This file
proves it unconditionally:

  graphIso_holds (h : Polynomial ℚ) : Mzk1G1B1SmoothCriterionSubmActual.GraphIso h

i.e.  Nonempty (smoothModelRing h ≃ₐ[Polynomial ℚ] Localization.Away (hDerivElt h)),
where smoothModelRing h = ℚ[λ][T,Z]/(λ - h(T), h'(T)Z - 1) and Localization.Away (hDerivElt h) is
ℚ[t][1/h'] on the renamed t-line chartT h = MvPolynomial (Fin 1) ℚ.

## Strategy (two-sided AlgEquiv.ofAlgHom, no ideal bookkeeping)

* psi : smoothModelRing h →ₐ[ℚ[λ]] ℚ[t][1/h'] is induced by T ↦ t, Z ↦ (h'(t))⁻¹
  (Ideal.Quotient.liftₐ from MvPolynomial.aeval); the two relations are killed because
  aeval T h = h(T) and aeval T h' = h'(T) (the bridges below) and h'(t)·h'(t)⁻¹ = 1
  (IsLocalization.Away.mul_invSelf).
* chi : ℚ[t][1/h'] →ₐ[ℚ[λ]] smoothModelRing h is IsLocalization.Away.lift with T ↦ T̄, its
  hypothesis h'(t) invertible being smoothModel_deriv_isUnit of the donor (transported by
  the bridge h'(T) = aeval T h').
* psi ∘ chi = id is free (IsLocalization.algHom_subsingleton), and chi ∘ psi = id is checked on
  the two generators of the model ring: T ↦ T̄ ↦ T̄, and Z ↦ h'(t)⁻¹ ↦ Z̄ by cancellation of the
  unit h'(T)̄ in h'(T)̄·Z̄ = 1.

## Contents (no sorry, no admit, no new axiom)

bridges hAtT_eq_aeval, pderiv_aeval_X0_derivative, hDerivAtT_eq_aeval: the donor's explicit
Finset.sum definitions of h(T), h'(T) agree with Polynomial.aeval at T = X 0 (the second via the
one-variable chain rule for MvPolynomial.pderiv, proved here by induction on the polynomial);
map_aeval_apply: an ℚ[λ]-algebra hom is in particular ℚ-linear, hence commutes with
Polynomial.aeval; then the two maps, the two round trips, graphIsoEquiv and graphIso_holds.
-/
import tmp.sheaf.xif.paper.Mzk1G1B1SmoothCriterionSubmActual
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1B1SmoothCriterionSubmActual

namespace LeanFormal.IUT.XiFPaper.Mzk1G1B1GraphIsoModelActual

/-! ## 0. Notation -/

/-- The polynomial ring ℚ[λ][T,Z] in which the two relations live. -/
abbrev ModelPoly : Type := MvPolynomial (Fin 2) (Polynomial ℚ)

/-- Fin 2 has exactly the two elements 0 and 1. -/
theorem fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  rcases i with ⟨n, hn⟩
  have h : n = 0 ∨ n = 1 := by omega
  rcases h with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

/-! ## 1. The three bridges -/

/-- **Bridge (i).**  The donor's explicit sum hAtT h = Σ h_i T^i is h evaluated at T = X 0.
(The two sides have the same summands: algebraMap ℚ ℚ[λ][T,Z] is C ∘ C definitionally.) -/
theorem hAtT_eq_aeval (h : Polynomial ℚ) :
    hAtT h = Polynomial.aeval (MvPolynomial.X 0) h := by
  rw [hAtT, Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1

/-- **The one-variable chain rule** for MvPolynomial.pderiv: ∂_T (p(T)) = p'(T). -/
theorem pderiv_aeval_X0_derivative (p : Polynomial ℚ) :
    MvPolynomial.pderiv (0 : Fin 2)
        (Polynomial.aeval (MvPolynomial.X 0 : ModelPoly) p)
      = Polynomial.aeval (MvPolynomial.X 0 : ModelPoly) (Polynomial.derivative p) := by
  have key : ∀ q : Polynomial ℚ,
      MvPolynomial.pderiv (0 : Fin 2) (Polynomial.aeval (MvPolynomial.X 0 : ModelPoly) q)
        = Polynomial.aeval (MvPolynomial.X 0 : ModelPoly) (Polynomial.derivative q) →
      MvPolynomial.pderiv (0 : Fin 2)
          (Polynomial.aeval (MvPolynomial.X 0 : ModelPoly) (q * Polynomial.X))
        = Polynomial.aeval (MvPolynomial.X 0 : ModelPoly)
            (Polynomial.derivative (q * Polynomial.X)) := by
    intro q hq
    rw [Polynomial.derivative_mul, Polynomial.derivative_X, mul_one]
    simp only [map_mul, map_add, Polynomial.aeval_X, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_X_self, hq, mul_one]
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro a
    rw [Polynomial.derivative_C, Polynomial.aeval_C, map_zero,
      IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) ModelPoly,
      MvPolynomial.algebraMap_eq, Polynomial.algebraMap_eq, MvPolynomial.pderiv_C]
  · intro p q hp hq
    rw [Polynomial.derivative_add]
    simp only [map_add, hp, hq]
  · intro n a ih
    rw [pow_succ, ← mul_assoc]
    exact key _ ih

/-- **Bridge (ii).**  The donor's explicit sum hDerivAtT h = Σ i h_i T^{i-1} is h' evaluated
at T = X 0.  Immediate from pderiv_hAtT, bridge (i) and the chain rule above. -/
theorem hDerivAtT_eq_aeval (h : Polynomial ℚ) :
    hDerivAtT h = Polynomial.aeval (MvPolynomial.X 0) (Polynomial.derivative h) := by
  rw [← pderiv_hAtT h, hAtT_eq_aeval h, pderiv_aeval_X0_derivative]

/-- **Bridge (iii).**  An ℚ[λ]-algebra hom is in particular a ℚ-algebra hom, hence commutes
with Polynomial.aeval (which is taken over ℚ, the coefficient ring of Polynomial ℚ). -/
theorem map_aeval_apply {B : Type*} [CommRing B] [Algebra (Polynomial ℚ) B] [Algebra ℚ B]
    [IsScalarTower ℚ (Polynomial ℚ) B]
    (f : ModelPoly →ₐ[Polynomial ℚ] B) (x : ModelPoly) (p : Polynomial ℚ) :
    f (Polynomial.aeval x p) = Polynomial.aeval (f x) p := by
  have hcomp : (algebraMap (Polynomial ℚ) B).comp (algebraMap ℚ (Polynomial ℚ))
      = (f : ModelPoly →+* B).comp (algebraMap ℚ ModelPoly) := by
    refine RingHom.ext fun r => ?_
    have h1 := RingHom.congr_fun (AlgHom.comp_algebraMap_of_tower (R := ℚ) f) r
    simp only [RingHom.comp_apply] at h1 ⊢
    rw [← IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) B r]
    exact h1.symm
  have hstep := Polynomial.map_aeval_eq_aeval_map (R := ℚ) (S := ModelPoly) (T := Polynomial ℚ)
    (U := B) (φ := algebraMap ℚ (Polynomial ℚ)) (ψ := (f : ModelPoly →+* B)) hcomp p x
  have hstep2 := Polynomial.aeval_map_algebraMap (Polynomial ℚ) ((f : ModelPoly →+* B) x) p
  exact hstep.trans hstep2

/-! ## 2. The map out of the model ring: T ↦ t, Z ↦ h'(t)⁻¹ -/

/-- The evaluation map on ℚ[λ][T,Z] underlying the graph isomorphism. -/
noncomputable def smoothModelEval (h : Polynomial ℚ) :
    ModelPoly →ₐ[Polynomial ℚ] Localization.Away (hDerivElt h) :=
  MvPolynomial.aeval (fun i : Fin 2 =>
    if i = 0 then algebraMap (chartT h) (Localization.Away (hDerivElt h)) (MvPolynomial.X 0)
    else IsLocalization.Away.invSelf (hDerivElt h))

theorem smoothModelEval_X0 (h : Polynomial ℚ) :
    smoothModelEval h (MvPolynomial.X 0)
      = algebraMap (chartT h) (Localization.Away (hDerivElt h)) (MvPolynomial.X 0) := by
  rw [smoothModelEval, MvPolynomial.aeval_X]
  exact if_pos rfl

theorem smoothModelEval_X1 (h : Polynomial ℚ) :
    smoothModelEval h (MvPolynomial.X 1)
      = IsLocalization.Away.invSelf (hDerivElt h) := by
  rw [smoothModelEval, MvPolynomial.aeval_X]
  exact if_neg (by decide)

/-- The first relation λ - h(T) is killed: h(T) ↦ h(t). -/
theorem smoothModelEval_rel_zero (h : Polynomial ℚ) :
    smoothModelEval h (smoothModelRel h 0) = 0 := by
  have hC : smoothModelEval h (MvPolynomial.C Polynomial.X)
      = algebraMap (Polynomial ℚ) (Localization.Away (hDerivElt h)) Polynomial.X := by
    rw [smoothModelEval, MvPolynomial.aeval_C]
  have hT : smoothModelEval h (hAtT h)
      = algebraMap (chartT h) (Localization.Away (hDerivElt h)) (hElt h) := by
    rw [hAtT_eq_aeval h, map_aeval_apply (smoothModelEval h) (MvPolynomial.X 0) h,
      smoothModelEval_X0, Polynomial.aeval_algebraMap_apply]
    rfl
  rw [smoothModelRel_zero, map_sub, hC, hT, sub_eq_zero,
    IsScalarTower.algebraMap_apply (Polynomial ℚ) (chartT h)
      (Localization.Away (hDerivElt h)) Polynomial.X,
    ← algebraMap_X h]

/-- The second relation h'(T)Z - 1 is killed, since Z ↦ h'(t)⁻¹. -/
theorem smoothModelEval_rel_one (h : Polynomial ℚ) :
    smoothModelEval h (smoothModelRel h 1) = 0 := by
  have hD : smoothModelEval h (hDerivAtT h)
      = algebraMap (chartT h) (Localization.Away (hDerivElt h)) (hDerivElt h) := by
    rw [hDerivAtT_eq_aeval h,
      map_aeval_apply (smoothModelEval h) (MvPolynomial.X 0) (Polynomial.derivative h),
      smoothModelEval_X0, Polynomial.aeval_algebraMap_apply]
    rfl
  rw [smoothModelRel_one, map_sub, map_mul, map_one, hD, smoothModelEval_X1,
    IsLocalization.Away.mul_invSelf, sub_self]

/-- Both relations are killed by smoothModelEval h. -/
theorem smoothModelEval_rel_mem (h : Polynomial ℚ) :
    ∀ a : ModelPoly, a ∈ Ideal.span (Set.range (smoothModelRel h)) →
      smoothModelEval h a = 0 := by
  have hle : Ideal.span (Set.range (smoothModelRel h))
      ≤ RingHom.ker (smoothModelEval h).toRingHom := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    refine RingHom.mem_ker.mpr ?_
    rcases fin_two_cases i with hi | hi
    · rw [hi]; exact smoothModelEval_rel_zero h
    · rw [hi]; exact smoothModelEval_rel_one h
  intro a ha
  exact RingHom.mem_ker.mp (hle ha)

/-- The substitution T ↦ t, Z ↦ h'(t)⁻¹, well defined on the model ring. -/
noncomputable def smoothModelToAway (h : Polynomial ℚ) :
    smoothModelRing h →ₐ[Polynomial ℚ] Localization.Away (hDerivElt h) :=
  Ideal.Quotient.liftₐ (Ideal.span (Set.range (smoothModelRel h))) (smoothModelEval h)
    (smoothModelEval_rel_mem h)

/-- Values of smoothModelToAway on classes. -/
theorem smoothModelToAway_mk (h : Polynomial ℚ) (a : ModelPoly) :
    smoothModelToAway h
        (Ideal.Quotient.mkₐ (Polynomial ℚ) (Ideal.span (Set.range (smoothModelRel h))) a)
      = smoothModelEval h a :=
  AlgHom.congr_fun
    (Ideal.Quotient.liftₐ_comp (Ideal.span (Set.range (smoothModelRel h))) (smoothModelEval h)
      (smoothModelEval_rel_mem h)) a

/-! ## 3. The map into the model ring: t ↦ T̄ -/

/-- The class of T in the model ring. -/
noncomputable def smoothModelT (h : Polynomial ℚ) : smoothModelRing h :=
  Ideal.Quotient.mk (Ideal.span (Set.range (smoothModelRel h))) (MvPolynomial.X 0)

/-- The class of Z in the model ring. -/
noncomputable def smoothModelZ (h : Polynomial ℚ) : smoothModelRing h :=
  Ideal.Quotient.mk (Ideal.span (Set.range (smoothModelRel h))) (MvPolynomial.X 1)

/-- t ↦ T̄, as a ℚ-algebra map. -/
noncomputable def chartToModel (h : Polynomial ℚ) : chartT h →ₐ[ℚ] smoothModelRing h :=
  MvPolynomial.aeval (fun _ : Fin 1 => smoothModelT h)

theorem chartToModel_X (h : Polynomial ℚ) :
    chartToModel h (MvPolynomial.X 0) = smoothModelT h := by
  rw [chartToModel, MvPolynomial.aeval_X]

/-- Evaluation at T̄ of the class of h(T) is the class of h(T), by bridge (i). -/
theorem mk_aeval_X0 (h : Polynomial ℚ) (p : Polynomial ℚ) :
    Ideal.Quotient.mkₐ (Polynomial ℚ) (Ideal.span (Set.range (smoothModelRel h)))
        (Polynomial.aeval (MvPolynomial.X 0) p)
      = Polynomial.aeval (smoothModelT h) p :=
  map_aeval_apply (B := smoothModelRing h)
    (Ideal.Quotient.mkₐ (Polynomial ℚ) (Ideal.span (Set.range (smoothModelRel h))))
    (MvPolynomial.X 0) p

/-- h(T̄) = λ̄: the class of h(T) is the class of C λ (the first relation). -/
theorem aeval_tm_eq_algebraMap_X (h : Polynomial ℚ) :
    Polynomial.aeval (smoothModelT h) h
      = algebraMap (Polynomial ℚ) (smoothModelRing h) Polynomial.X := by
  have h0 : Ideal.Quotient.mk (Ideal.span (Set.range (smoothModelRel h)))
      (smoothModelRel h 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (smoothModel_relation_mem h 0)
  rw [smoothModelRel_zero, map_sub, sub_eq_zero] at h0
  rw [← mk_aeval_X0 h h, ← hAtT_eq_aeval h]
  have hmap : algebraMap (Polynomial ℚ) (smoothModelRing h) Polynomial.X
      = Ideal.Quotient.mk (Ideal.span (Set.range (smoothModelRel h)))
          (MvPolynomial.C Polynomial.X) := rfl
  rw [hmap]
  exact h0.symm

/-- h'(T̄) is the class of h'(T). -/
theorem chartToModel_hDerivElt (h : Polynomial ℚ) :
    chartToModel h (hDerivElt h)
      = Ideal.Quotient.mk (Ideal.span (Set.range (smoothModelRel h))) (hDerivAtT h) := by
  have h1 : chartToModel h (hDerivElt h)
      = Polynomial.aeval (smoothModelT h) (Polynomial.derivative h) := by
    rw [show hDerivElt h
        = Polynomial.aeval (MvPolynomial.X 0 : chartT h) (Polynomial.derivative h) from rfl,
      ← Polynomial.aeval_algHom_apply (chartToModel h) (MvPolynomial.X 0 : chartT h)
        (Polynomial.derivative h),
      chartToModel_X]
  rw [h1, ← mk_aeval_X0 h (Polynomial.derivative h), ← hDerivAtT_eq_aeval h]
  rfl

/-- h'(T̄) is a unit of the model ring (the second relation). -/
theorem chartToModel_hDerivElt_isUnit (h : Polynomial ℚ) :
    IsUnit (chartToModel h (hDerivElt h)) := by
  rw [chartToModel_hDerivElt h]
  exact smoothModel_deriv_isUnit h

/-- The substitution t ↦ T̄ is ℚ[λ]-linear: λ ↦ h(t) ↦ h(T̄) = λ̄. -/
theorem chartToModel_algebraMap (h : Polynomial ℚ) (r : Polynomial ℚ) :
    chartToModel h (algebraMap (Polynomial ℚ) (chartT h) r)
      = algebraMap (Polynomial ℚ) (smoothModelRing h) r := by
  have h1 : algebraMap (Polynomial ℚ) (chartT h) r = Polynomial.aeval (hElt h) r := by
    rw [algebraMap_eq h, chartMap]
    simp
  have h2 : chartToModel h (hElt h)
      = algebraMap (Polynomial ℚ) (smoothModelRing h) Polynomial.X := by
    have h3 : chartToModel h (hElt h) = Polynomial.aeval (smoothModelT h) h := by
      rw [show hElt h = Polynomial.aeval (MvPolynomial.X 0 : chartT h) h from rfl,
        ← Polynomial.aeval_algHom_apply (chartToModel h) (MvPolynomial.X 0 : chartT h) h,
        chartToModel_X]
    rw [h3, aeval_tm_eq_algebraMap_X h]
  rw [h1, ← Polynomial.aeval_algHom_apply (chartToModel h) (hElt h) r, h2,
    Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]

/-- The chart substitution t ↦ T̄ upgraded to a ℚ[λ]-algebra hom (its ℚ[λ]-linearity is
`chartToModel_algebraMap`).  This is the map fed to `IsLocalization.Away.liftAlgHom`. -/
noncomputable def chartToModelA (h : Polynomial ℚ) :
    chartT h →ₐ[Polynomial ℚ] smoothModelRing h where
  toFun := fun a => chartToModel h a
  map_one' := map_one (chartToModel h)
  map_mul' := map_mul (chartToModel h)
  map_zero' := map_zero (chartToModel h)
  map_add' := map_add (chartToModel h)
  commutes' := chartToModel_algebraMap h

/-! ## 4. The map out of the localization: t ↦ T̄ -/

/-- The function underlying `smoothModelFromAway`: the extension of t ↦ T̄ to the
localization, which exists because h'(T̄) is a unit of the model ring. -/
noncomputable def smoothModelFromAwayHom (h : Polynomial ℚ)
    (s : Localization.Away (hDerivElt h)) : smoothModelRing h :=
  IsLocalization.Away.lift (x := hDerivElt h) (g := (chartToModel h).toRingHom)
    (chartToModel_hDerivElt_isUnit h) s

/-- Values of that function on the image of ℚ[t]. -/
theorem smoothModelFromAwayHom_algebraMap (h : Polynomial ℚ) (a : chartT h) :
    smoothModelFromAwayHom h
        (algebraMap (chartT h) (Localization.Away (hDerivElt h)) a)
      = chartToModel h a := by
  simp only [smoothModelFromAwayHom, IsLocalization.Away.lift_eq]
  rfl

/-- **The map from ℚ[t][1/h'] into the model ring**, T ↦ T̄ (the extension of t ↦ T̄ to the
localization, its hypothesis being that h'(T̄) is a unit). -/
noncomputable def smoothModelFromAway (h : Polynomial ℚ) :
    Localization.Away (hDerivElt h) →ₐ[Polynomial ℚ] smoothModelRing h where
  toFun := smoothModelFromAwayHom h
  map_one' := by simp only [smoothModelFromAwayHom, map_one]
  map_mul' := by intro p q; simp only [smoothModelFromAwayHom, map_mul]
  map_zero' := by simp only [smoothModelFromAwayHom, map_zero]
  map_add' := by intro p q; simp only [smoothModelFromAwayHom, map_add]
  commutes' := by
    intro r
    rw [IsScalarTower.algebraMap_apply (Polynomial ℚ) (chartT h)
      (Localization.Away (hDerivElt h)) r]
    exact (smoothModelFromAwayHom_algebraMap h
      (algebraMap (Polynomial ℚ) (chartT h) r)).trans (chartToModel_algebraMap h r)

/-- Values of smoothModelFromAway on the image of ℚ[t]. -/
theorem fromAway_algebraMap (h : Polynomial ℚ) (a : chartT h) :
    smoothModelFromAway h
        (algebraMap (chartT h) (Localization.Away (hDerivElt h)) a)
      = chartToModel h a :=
  smoothModelFromAwayHom_algebraMap h a

/-! ## 5. The two round trips -/

/-- χ ∘ ψ = id: on T this is chartToModel_X, on Z it is the cancellation of the unit h'(T̄). -/
theorem fromAway_comp_toAway (h : Polynomial ℚ) :
    (smoothModelFromAway h).comp (smoothModelToAway h)
      = AlgHom.id (Polynomial ℚ) (smoothModelRing h) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, AlgHom.id_apply]
  rcases fin_two_cases i with hi | hi
  · rw [hi, smoothModelToAway_mk, smoothModelEval_X0, fromAway_algebraMap, chartToModel_X]
    rfl
  · rw [hi, smoothModelToAway_mk, smoothModelEval_X1]
    have hrel : chartToModel h (hDerivElt h) * smoothModelZ h = 1 := by
      have h0 : Ideal.Quotient.mk (Ideal.span (Set.range (smoothModelRel h)))
          (smoothModelRel h 1) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (smoothModel_relation_mem h 1)
      rw [smoothModelRel_one, map_sub, map_mul, map_one, sub_eq_zero] at h0
      rw [chartToModel_hDerivElt h]
      exact h0
    have hmul : chartToModel h (hDerivElt h)
        * smoothModelFromAway h (IsLocalization.Away.invSelf (hDerivElt h)) = 1 := by
      rw [← fromAway_algebraMap h (hDerivElt h), ← map_mul,
        IsLocalization.Away.mul_invSelf, map_one]
    have hcancel := (IsUnit.mul_right_inj (chartToModel_hDerivElt_isUnit h)).mp
      (hmul.trans hrel.symm)
    rw [hcancel]
    rfl

/-- ψ sends the constants of ℚ[t] to themselves. -/
theorem toAway_chartToModel_C (h : Polynomial ℚ) (r : ℚ) :
    smoothModelToAway h (chartToModel h (MvPolynomial.C r))
      = algebraMap (chartT h) (Localization.Away (hDerivElt h)) (MvPolynomial.C r) := by
  have h1 : chartToModel h (MvPolynomial.C r) = algebraMap ℚ (smoothModelRing h) r := by
    rw [chartToModel, MvPolynomial.aeval_C]
  rw [h1, AlgHom.map_algebraMap, ← MvPolynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply ℚ (chartT h) (Localization.Away (hDerivElt h)) r]

/-- ψ sends the class of the variable t to t (the class of T is the canonical image of t). -/
theorem toAway_smoothModelT (h : Polynomial ℚ) :
    smoothModelToAway h (smoothModelT h)
      = algebraMap (chartT h) (Localization.Away (hDerivElt h)) (MvPolynomial.X 0) := by
  have h1 : smoothModelT h
      = Ideal.Quotient.mkₐ (Polynomial ℚ) (Ideal.span (Set.range (smoothModelRel h)))
          (MvPolynomial.X 0) := rfl
  rw [h1, smoothModelToAway_mk, smoothModelEval_X0]

/-- ψ sends the image of the variable t to t. -/
theorem toAway_chartToModel_X (h : Polynomial ℚ) (i : Fin 1) :
    smoothModelToAway h (chartToModel h (MvPolynomial.X i))
      = algebraMap (chartT h) (Localization.Away (hDerivElt h)) (MvPolynomial.X i) := by
  have hi : i = 0 := Subsingleton.elim i 0
  rw [hi, chartToModel_X, toAway_smoothModelT]

/-- ψ is the identity on the image of ℚ[t] in ℚ[t][1/h']. -/
theorem toAway_chartToModel (h : Polynomial ℚ) (a : chartT h) :
    smoothModelToAway h (chartToModel h a)
      = algebraMap (chartT h) (Localization.Away (hDerivElt h)) a := by
  induction a using MvPolynomial.induction_on with
  | C r => exact toAway_chartToModel_C h r
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, toAway_chartToModel_X h i]

/-- ψ ∘ χ = id: both are ring homs out of the localization ℚ[t][1/h'] and they agree on ℚ[t]
(IsLocalization.ringHom_ext). -/
theorem toAway_comp_fromAway (h : Polynomial ℚ) :
    (smoothModelToAway h).comp (smoothModelFromAway h)
      = AlgHom.id (Polynomial ℚ) (Localization.Away (hDerivElt h)) := by
  have hkey : (smoothModelToAway h).toRingHom.comp (smoothModelFromAway h).toRingHom
      = RingHom.id (Localization.Away (hDerivElt h)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (hDerivElt h)) ?_
    refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply, RingHom.id_apply]
    show smoothModelToAway h (smoothModelFromAway h
        (algebraMap (chartT h) (Localization.Away (hDerivElt h)) a))
      = algebraMap (chartT h) (Localization.Away (hDerivElt h)) a
    rw [fromAway_algebraMap, toAway_chartToModel]
  exact AlgHom.ext fun x => RingHom.congr_fun hkey x

/-! ## 6. The graph isomorphism and the target -/

/-- **P2, algebra form.**  The submersive model ring is the localization of the renamed t-line at
h': ℚ[λ][T,Z]/(λ - h(T), h'(T)Z - 1) ≃ₐ[ℚ[λ]] ℚ[t][1/h']. -/
noncomputable def graphIsoEquiv (h : Polynomial ℚ) :
    smoothModelRing h ≃ₐ[Polynomial ℚ] Localization.Away (hDerivElt h) :=
  AlgEquiv.ofAlgHom (smoothModelToAway h) (smoothModelFromAway h)
    (toAway_comp_fromAway h) (fromAway_comp_toAway h)

/-- **P2, target form.**  The graph isomorphism of route (b) holds for every h : ℚ[λ], hence
the reduction smoothAt_of_derivative_notMem becomes unconditional. -/
theorem graphIso_holds (h : Polynomial ℚ) : GraphIso h :=
  ⟨graphIsoEquiv h⟩

/-! ## 7. Axiom checks -/

#print axioms fin_two_cases
#print axioms hAtT_eq_aeval
#print axioms pderiv_aeval_X0_derivative
#print axioms hDerivAtT_eq_aeval
#print axioms map_aeval_apply
#print axioms smoothModelEval_X0
#print axioms smoothModelEval_X1
#print axioms smoothModelEval_rel_zero
#print axioms smoothModelEval_rel_one
#print axioms smoothModelEval_rel_mem
#print axioms smoothModelToAway_mk
#print axioms chartToModel_X
#print axioms mk_aeval_X0
#print axioms aeval_tm_eq_algebraMap_X
#print axioms chartToModel_hDerivElt
#print axioms chartToModel_hDerivElt_isUnit
#print axioms chartToModel_algebraMap
#print axioms chartToModelA
#print axioms smoothModelFromAwayHom
#print axioms smoothModelFromAwayHom_algebraMap
#print axioms fromAway_algebraMap
#print axioms toAway_chartToModel_C
#print axioms toAway_smoothModelT
#print axioms toAway_chartToModel_X
#print axioms toAway_chartToModel
#print axioms fromAway_comp_toAway
#print axioms toAway_comp_fromAway
#print axioms graphIsoEquiv
#print axioms graphIso_holds

end LeanFormal.IUT.XiFPaper.Mzk1G1B1GraphIsoModelActual
