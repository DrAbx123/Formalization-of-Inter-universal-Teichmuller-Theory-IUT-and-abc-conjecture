/-
# B1 — direction B of the smooth ↔ derivative criterion, via the submersive model (route (b))

Consumer: Mzk1G1B1HPolySmoothLocusActual.SmoothCriterion / hbridge (the hbridge lane
Mzk1G1B1HPolyBranchSchemeActual → Mzk1G1B1HbObligationsActual →
Mzk1G1PhiFixedLBranchSupportActual), and the scheme bridge
Mzk1G1B1HPolySmoothLocusActual.chartInf_smoothLocus_iff_specMap.

## Goal

Direction **B** of SmoothCriterion h for the t-chart chartMorphismInf h = Spec.map (evalAt h) ≫
localChartInf: for a prime q of the t-line ℚ[t] with h' ∉ q, the t-chart is (formally) smooth at q.
Ring level this is: ℚ[t] is formally smooth over ℚ[λ] (via λ ↦ h(t)) at every prime where the
derivative h' is invertible.

## Why the submersive model (route (b), Lead 裁)

Doing it naively on Polynomial ℚ runs into the *same-type algebra diamond* diagnosed in
Mzk1G1B1SmoothCriterionActual: evalAt h : ℚ[λ] →+* ℚ[t] has source and target both the type
Polynomial ℚ, so evalAlg h collides with the identity/localization structures.  We therefore work
with the **renamed t-line**  chartT h := MvPolynomial (Fin 1) ℚ  (an abbrev, but a *different* ring
from Polynomial ℚ), carrying the ℚ[λ]-algebra structure λ ↦ h(t).  On this renamed copy there is no
competing structure, so IsLocalization, IsScalarTower, FormallySmooth etc. all behave.

The submersive model of route (b) is
  smoothModelRing h := ℚ[λ][T,Z] / (λ - h(T), h'(T)·Z - 1)
(smoothModelRel h 0 = C λ - h(T), smoothModelRel h 1 = h'(T)·Z - 1), over the base ring
Polynomial ℚ = ℚ[λ].  Its 2 × 2 Jacobian is
  det = (-h'(T)) · h'(T) - (∂_T h'(T)) · 0 = -(h'(T))²
and the second relation h'(T)·Z = 1 makes h'(T) a unit of the model ring, hence the Jacobian is a
unit.  Thus the model is standard smooth of relative dimension 2 - 2 = 0 over ℚ[λ], hence
Algebra.Smooth, hence Algebra.FormallySmooth.

## What is proved here (no sorry, no admit, no new axiom)

1. hAtT / hDerivAtT: h(T) and h'(T) in ℚ[λ][T,Z], written as explicit sums
   sum_{i ≤ deg h} h_i T^i and sum_{i ≤ deg h} h_i · i · T^{i-1}; pderiv_hAtT:
   ∂_T (h(T)) = h'(T), and the vanishing of the Z-derivatives of both (pderiv_one_hAtT,
   pderiv_one_hDerivAtT).
2. smoothModel_jacobiMatrix_*, smoothModel_det, smoothModel_deriv_isUnit,
   smoothModel_jacobian_isUnit: the Jacobian computation and its invertibility.
3. smoothModelPresentation, smoothModel_isStandardSmoothOfRelativeDimension (relative dimension 0),
   smoothModel_isStandardSmooth, smoothModel_smooth (Algebra.Smooth) and smoothModel_formallySmooth
   (Algebra.FormallySmooth) — **unconditional**.
4. The renamed t-line chartT h with its ℚ[λ]-algebra structure (chartMap, algebraMap_X), the
   general localization step isSmoothAt_of_formallySmooth (a formally smooth algebra is formally
   smooth at every prime), and the prime comparison (smoothAt_of_derivative_notMem): given the graph
   isomorphism GraphIso h (below) and a prime q with h' ∉ q, Algebra.IsSmoothAt ℚ[λ] q holds.

## The one missing ingredient (deliberately NOT assumed as an axiom)

GraphIso h, the *graph isomorphism of route (b)*:
  smoothModelRing h ≃ₐ[ℚ[λ]] ℚ[t][1/h'] = Localization.Away (h'(t)).
This is the substitution T ↦ t, Z ↦ h'(t)⁻¹ together with the exactness of the two relations
(ker = span), i.e. the graph isomorphism ℚ[λ][T]/(λ - h(T)) ≅ ℚ[t] composed with
C[Z]/(gZ - 1) ≅ C[1/g].  Pieces that Mathlib already has for it:
Polynomial.quotientSpanXSubCAlgEquiv, IsLocalization.adjoin_inv, Localization.awayEquivAdjoin; the
remaining work is the ideal-quotient bookkeeping (MvPolynomial.quotientEquiv-style) that carries
(λ - h(T), h'(T)Z - 1) across the rearrangement ℚ[λ][T,Z] ≅ ℚ[T][λ,Z].  It is stated here as the
hypothesis GraphIso h of smoothAt_of_derivative_notMem; that theorem is a *reduction*, not an
unconditional claim.

No sorry, no admit, no new axiom: every declaration below is proved, the conditional ones carry
GraphIso h explicitly in their statement.
-/
import Mathlib.RingTheory.Extension.Presentation.Submersive
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1B1SmoothCriterionSubmActual

/-! ## 1. The model ℚ[λ][T,Z] / (λ - h(T), h'(T)·Z - 1) -/

/-- h(T) ∈ ℚ[λ][T,Z]: the polynomial h evaluated at the variable T = X 0, as the explicit sum
sum_{i ≤ deg h} h_i · T^i.  (It equals Polynomial.aeval (MvPolynomial.X 0) h.) -/
noncomputable def hAtT (h : Polynomial ℚ) : MvPolynomial (Fin 2) (Polynomial ℚ) :=
  Finset.sum (Finset.range (h.natDegree + 1))
    (fun i => MvPolynomial.C (Polynomial.C (h.coeff i)) * MvPolynomial.X 0 ^ i)

/-- h'(T) ∈ ℚ[λ][T,Z]: the formal derivative of h evaluated at T, as the explicit sum
sum_{i ≤ deg h} h_i · i · T^(i-1).  It is ∂_T (h(T)) (pderiv_hAtT). -/
noncomputable def hDerivAtT (h : Polynomial ℚ) : MvPolynomial (Fin 2) (Polynomial ℚ) :=
  Finset.sum (Finset.range (h.natDegree + 1))
    (fun i => MvPolynomial.C (Polynomial.C (h.coeff i)) *
      ((i : MvPolynomial (Fin 2) (Polynomial ℚ)) * MvPolynomial.X 0 ^ (i - 1)))

/-- **The T-derivative of h(T) is h'(T).** -/
theorem pderiv_hAtT (h : Polynomial ℚ) :
    MvPolynomial.pderiv 0 (hAtT h) = hDerivAtT h := by
  simp only [hAtT, hDerivAtT]
  rw [map_sum (MvPolynomial.pderiv (0 : Fin 2))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_self, mul_one]

/-- h(T) does not involve Z, so its Z-derivative vanishes. -/
theorem pderiv_one_hAtT (h : Polynomial ℚ) :
    MvPolynomial.pderiv 1 (hAtT h) = 0 := by
  simp only [hAtT]
  rw [map_sum (MvPolynomial.pderiv (1 : Fin 2))]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1)]
  simp

/-- h'(T) does not involve Z, so its Z-derivative vanishes. -/
theorem pderiv_one_hDerivAtT (h : Polynomial ℚ) :
    MvPolynomial.pderiv 1 (hDerivAtT h) = 0 := by
  simp only [hDerivAtT]
  rw [map_sum (MvPolynomial.pderiv (1 : Fin 2))]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_mul]
  rw [show ((i : MvPolynomial (Fin 2) (Polynomial ℚ)))
      = MvPolynomial.C ((i : Polynomial ℚ)) from (MvPolynomial.C_eq_coe_nat i).symm]
  rw [MvPolynomial.pderiv_C, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1)]
  simp

/-- The two relations: λ - h(T) (i = 0) and h'(T)·Z - 1 (i = 1). -/
noncomputable def smoothModelRel (h : Polynomial ℚ) (i : Fin 2) :
    MvPolynomial (Fin 2) (Polynomial ℚ) :=
  if i = 0 then MvPolynomial.C Polynomial.X - hAtT h
  else hDerivAtT h * MvPolynomial.X 1 - 1

/-- Relation i differentiates against the variable T (i = 0) resp. Z (i = 1). -/
def smoothModelIdx (i : Fin 2) : Fin 2 := i

theorem smoothModelIdx_injective : Function.Injective smoothModelIdx := fun _ _ h => h

theorem smoothModelRel_zero (h : Polynomial ℚ) :
    smoothModelRel h 0 = MvPolynomial.C Polynomial.X - hAtT h := by
  simp [smoothModelRel]

theorem smoothModelRel_one (h : Polynomial ℚ) :
    smoothModelRel h 1 = hDerivAtT h * MvPolynomial.X 1 - 1 := by
  simp [smoothModelRel, show ¬ ((1 : Fin 2) = 0) from by decide]

theorem smoothModelIdx_zero : smoothModelIdx 0 = (0 : Fin 2) := rfl

theorem smoothModelIdx_one : smoothModelIdx 1 = (1 : Fin 2) := rfl

/-- The model ring ℚ[λ][T,Z] / (λ - h(T), h'(T)·Z - 1) of route (b). -/
noncomputable abbrev smoothModelRing (h : Polynomial ℚ) : Type :=
  MvPolynomial (Fin 2) (Polynomial ℚ) ⧸ Ideal.span (Set.range (smoothModelRel h))

/-- The naive pre-submersive presentation of the model ring: 2 variables, 2 relations. -/
noncomputable abbrev smoothModelPre (h : Polynomial ℚ) :
    Algebra.PreSubmersivePresentation (Polynomial ℚ) (smoothModelRing h) (Fin 2) (Fin 2) :=
  Algebra.PreSubmersivePresentation.naive (v := smoothModelRel h) smoothModelIdx
    smoothModelIdx_injective

/-! ### 2. The Jacobian -/

theorem smoothModel_jacobiMatrix_zero_zero (h : Polynomial ℚ) :
    (smoothModelPre h).jacobiMatrix 0 0 = - hDerivAtT h := by
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_naive, smoothModelRel_zero,
    smoothModelIdx_zero]
  rw [Derivation.map_sub, MvPolynomial.pderiv_C, zero_sub, pderiv_hAtT]

theorem smoothModel_jacobiMatrix_one_zero (h : Polynomial ℚ) :
    (smoothModelPre h).jacobiMatrix 1 0 = 0 := by
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_naive, smoothModelRel_zero,
    smoothModelIdx_one]
  rw [Derivation.map_sub, MvPolynomial.pderiv_C, zero_sub, pderiv_one_hAtT, neg_zero]

theorem smoothModel_jacobiMatrix_one_one (h : Polynomial ℚ) :
    (smoothModelPre h).jacobiMatrix 1 1 = hDerivAtT h := by
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_naive, smoothModelRel_one,
    smoothModelIdx_one]
  rw [Derivation.map_sub, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_one,
    pderiv_one_hDerivAtT, zero_mul, zero_add, MvPolynomial.pderiv_X_self, mul_one, sub_zero]

/-- The determinant of the Jacobian: -(h'(T))².  (The (0,1) entry is ∂_T ∂_T h(T)·Z, multiplied by
the vanishing (1,0) entry.) -/
theorem smoothModel_det (h : Polynomial ℚ) :
    (smoothModelPre h).jacobiMatrix.det = - (hDerivAtT h * hDerivAtT h) := by
  rw [Matrix.det_fin_two, smoothModel_jacobiMatrix_zero_zero, smoothModel_jacobiMatrix_one_one,
    smoothModel_jacobiMatrix_one_zero, mul_zero, sub_zero]
  ring

/-! ### 3. The Jacobian is a unit -/

theorem smoothModel_relation_mem (h : Polynomial ℚ) (i : Fin 2) :
    smoothModelRel h i ∈ Ideal.span (Set.range (smoothModelRel h)) :=
  Ideal.subset_span (Set.mem_range_self i)

/-- The second relation h'(T)·Z = 1 makes h'(T) a unit of the model ring. -/
theorem smoothModel_deriv_isUnit (h : Polynomial ℚ) :
    IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range (smoothModelRel h))) (hDerivAtT h)) := by
  have h0 : Ideal.Quotient.mk (Ideal.span (Set.range (smoothModelRel h))) (smoothModelRel h 1)
      = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (smoothModel_relation_mem h 1)
  rw [smoothModelRel_one, map_sub, map_mul, map_one, sub_eq_zero] at h0
  exact IsUnit.of_mul_eq_one _ h0

/-- The Jacobian -(h'(T))² is a unit of the model ring, so the presentation is submersive. -/
theorem smoothModel_jacobian_isUnit (h : Polynomial ℚ) :
    IsUnit (smoothModelPre h).jacobian := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, smoothModel_det,
    map_neg, map_mul]
  exact ((smoothModel_deriv_isUnit h).mul (smoothModel_deriv_isUnit h)).neg

/-- The submersive presentation of the model ring over ℚ[λ]. -/
noncomputable def smoothModelPresentation (h : Polynomial ℚ) :
    Algebra.SubmersivePresentation (Polynomial ℚ) (smoothModelRing h) (Fin 2) (Fin 2) where
  __ := smoothModelPre h
  jacobian_isUnit := smoothModel_jacobian_isUnit h

/-- **The model is standard smooth of relative dimension 0 over ℚ[λ].** -/
theorem smoothModel_isStandardSmoothOfRelativeDimension (h : Polynomial ℚ) :
    Algebra.IsStandardSmoothOfRelativeDimension 0 (Polynomial ℚ) (smoothModelRing h) := by
  refine Algebra.SubmersivePresentation.isStandardSmoothOfRelativeDimension
    (smoothModelPresentation h) ?_
  simp [Algebra.Presentation.dimension]

theorem smoothModel_isStandardSmooth (h : Polynomial ℚ) :
    Algebra.IsStandardSmooth (Polynomial ℚ) (smoothModelRing h) := by
  haveI := smoothModel_isStandardSmoothOfRelativeDimension h
  exact Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := 0)

/-- **The model is smooth over ℚ[λ].** -/
theorem smoothModel_smooth (h : Polynomial ℚ) :
    Algebra.Smooth (Polynomial ℚ) (smoothModelRing h) := by
  haveI := smoothModel_isStandardSmooth h
  infer_instance

/-- **The model is formally smooth over ℚ[λ]** (the algebraic core of direction B). -/
theorem smoothModel_formallySmooth (h : Polynomial ℚ) :
    Algebra.FormallySmooth (Polynomial ℚ) (smoothModelRing h) :=
  (smoothModel_smooth h).formallySmooth

/-! ## 4. The renamed t-line ℚ[t] with its ℚ[λ]-algebra structure λ ↦ h(t) -/

/-- The t-line ℚ[t], **renamed** so that it can carry the ℚ[λ]-algebra structure λ ↦ h(t) without
colliding with the identity structure on Polynomial ℚ (the diamond of
Mzk1G1B1SmoothCriterionActual). -/
abbrev chartT (h : Polynomial ℚ) : Type := MvPolynomial (Fin 1) ℚ

instance (h : Polynomial ℚ) : CommRing (chartT h) :=
  inferInstanceAs (CommRing (MvPolynomial (Fin 1) ℚ))

instance (h : Polynomial ℚ) : Algebra ℚ (chartT h) :=
  inferInstanceAs (Algebra ℚ (MvPolynomial (Fin 1) ℚ))

/-- h(t) ∈ ℚ[t]. -/
noncomputable def hElt (h : Polynomial ℚ) : chartT h :=
  Polynomial.aeval (MvPolynomial.X 0) h

/-- h'(t) ∈ ℚ[t]: the element that is inverted on the open set D(h'). -/
noncomputable def hDerivElt (h : Polynomial ℚ) : chartT h :=
  Polynomial.aeval (MvPolynomial.X 0) (Polynomial.derivative h)

/-- The structure map ℚ[λ] → ℚ[t], λ ↦ h(t). -/
noncomputable def chartMap (h : Polynomial ℚ) : Polynomial ℚ →+* chartT h :=
  (Polynomial.aeval (hElt h)).toRingHom

noncomputable instance (h : Polynomial ℚ) : Algebra (Polynomial ℚ) (chartT h) :=
  (chartMap h).toAlgebra

theorem algebraMap_eq (h : Polynomial ℚ) :
    algebraMap (Polynomial ℚ) (chartT h) = chartMap h :=
  RingHom.algebraMap_toAlgebra (chartMap h)

/-- The variable λ of the base maps to h(t). -/
theorem algebraMap_X (h : Polynomial ℚ) :
    algebraMap (Polynomial ℚ) (chartT h) Polynomial.X = hElt h := by
  rw [algebraMap_eq, chartMap]
  exact Polynomial.aeval_X (hElt h)

/-- **A formally smooth algebra is formally smooth at every prime** (localizing at a prime ideal is
a formally smooth localization, so formal smoothness composes). -/
theorem isSmoothAt_of_formallySmooth {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FormallySmooth R A] (p : Ideal A) [p.IsPrime] :
    Algebra.IsSmoothAt R p :=
  Algebra.FormallySmooth.comp R A (Localization.AtPrime p)

/-- **The missing graph isomorphism of route (b)** (see the file header): the submersive model is the
localization of the renamed t-line at h'.  Stated as a Prop so that the reduction below can be
proved unconditionally in it. -/
def GraphIso (h : Polynomial ℚ) : Prop :=
  Nonempty (smoothModelRing h ≃ₐ[Polynomial ℚ] Localization.Away (hDerivElt h))

/-- **Direction B of the smooth ↔ derivative criterion, ring level** (reduced to the graph
isomorphism GraphIso h): if the derivative h' is not in the prime q, then the ℚ[λ]-algebra ℚ[t]
(with λ ↦ h(t)) is formally smooth at q.

Proof: the model is formally smooth over ℚ[λ] (smoothModel_formallySmooth), hence so is ℚ[t][1/h']
(FormallySmooth.of_equiv along GraphIso h); localizing that at the prime p lying over q and
comparing (ℚ[t][1/h'])_p ≅ (ℚ[t])_q (IsLocalization.algEquiv, using h' ∉ q) gives the claim. -/
theorem smoothAt_of_derivative_notMem (h : Polynomial ℚ) (hG : GraphIso h)
    (q : PrimeSpectrum (chartT h)) (hq : hDerivElt h ∉ q.asIdeal) :
    Algebra.IsSmoothAt (Polynomial ℚ) q.asIdeal := by
  obtain ⟨e⟩ := hG
  haveI hmodel : Algebra.FormallySmooth (Polynomial ℚ) (smoothModelRing h) :=
    smoothModel_formallySmooth h
  haveI hfpModel : Algebra.FinitePresentation (Polynomial ℚ) (smoothModelRing h) :=
    (smoothModelPre h).toPresentation.finitePresentation_of_isFinite
  -- ℚ[t][1/h'] is formally smooth *and* finitely presented over ℚ[λ]
  haveI hfs : Algebra.FormallySmooth (Polynomial ℚ) (Localization.Away (hDerivElt h)) :=
    Algebra.FormallySmooth.of_equiv (A := smoothModelRing h)
      (B := Localization.Away (hDerivElt h)) e
  haveI hfp : Algebra.FinitePresentation (Polynomial ℚ) (Localization.Away (hDerivElt h)) :=
    Algebra.FinitePresentation.equiv (A := smoothModelRing h)
      (B := Localization.Away (hDerivElt h)) e
  -- hence its whole smooth locus is everything,
  have hU : Algebra.smoothLocus (Polynomial ℚ) (Localization.Away (hDerivElt h)) = Set.univ :=
    Algebra.smoothLocus_eq_univ_iff.mpr hfs
  -- and it is the preimage of the smooth locus of ℚ[t]
  have hcom : PrimeSpectrum.comap (algebraMap (chartT h) (Localization.Away (hDerivElt h)))
      ⁻¹' Algebra.smoothLocus (Polynomial ℚ) (chartT h)
      = Algebra.smoothLocus (Polynomial ℚ) (Localization.Away (hDerivElt h)) :=
    Algebra.smoothLocus_comap_of_isLocalization (R := Polynomial ℚ) (A := chartT h)
      (Af := Localization.Away (hDerivElt h)) (f := hDerivElt h)
  -- the prime of the localization lying over q
  let p : Ideal (Localization.Away (hDerivElt h)) :=
    q.asIdeal.map (algebraMap (chartT h) (Localization.Away (hDerivElt h)))
  have hdisj : Disjoint (Submonoid.powers (hDerivElt h) : Set (chartT h))
      (q.asIdeal : Set (chartT h)) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime (hDerivElt h)).mpr hq
  have hp : p.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (hDerivElt h))
      (Localization.Away (hDerivElt h)) q.asIdeal q.isPrime hdisj
  have hun : p.comap (algebraMap (chartT h) (Localization.Away (hDerivElt h))) = q.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers (hDerivElt h))
      (Localization.Away (hDerivElt h)) q.isPrime hdisj
  -- every prime of the localization is smooth, so its image in ℚ[t] is smooth at q
  have hP : (⟨p, hp⟩ : PrimeSpectrum (Localization.Away (hDerivElt h))) ∈
      Algebra.smoothLocus (Polynomial ℚ) (Localization.Away (hDerivElt h)) := by
    rw [hU]
    exact Set.mem_univ _
  have hqmem : q ∈ Algebra.smoothLocus (Polynomial ℚ) (chartT h) := by
    have h1 : (⟨p, hp⟩ : PrimeSpectrum (Localization.Away (hDerivElt h))) ∈
        PrimeSpectrum.comap (algebraMap (chartT h) (Localization.Away (hDerivElt h))) ⁻¹'
          Algebra.smoothLocus (Polynomial ℚ) (chartT h) := by
      rw [hcom]
      exact hP
    have h2 : PrimeSpectrum.comap (algebraMap (chartT h) (Localization.Away (hDerivElt h)))
        (⟨p, hp⟩ : PrimeSpectrum (Localization.Away (hDerivElt h))) ∈
          Algebra.smoothLocus (Polynomial ℚ) (chartT h) := h1
    rwa [show PrimeSpectrum.comap (algebraMap (chartT h) (Localization.Away (hDerivElt h)))
        (⟨p, hp⟩ : PrimeSpectrum (Localization.Away (hDerivElt h))) = q from
      PrimeSpectrum.ext hun] at h2
  exact hqmem

/-! ## 5. Axiom checks -/

#print axioms hAtT
#print axioms hDerivAtT
#print axioms pderiv_hAtT
#print axioms pderiv_one_hAtT
#print axioms pderiv_one_hDerivAtT
#print axioms smoothModelRel_zero
#print axioms smoothModelRel_one
#print axioms smoothModel_jacobiMatrix_zero_zero
#print axioms smoothModel_jacobiMatrix_one_zero
#print axioms smoothModel_jacobiMatrix_one_one
#print axioms smoothModel_det
#print axioms smoothModel_deriv_isUnit
#print axioms smoothModel_jacobian_isUnit
#print axioms smoothModel_isStandardSmoothOfRelativeDimension
#print axioms smoothModel_isStandardSmooth
#print axioms smoothModel_smooth
#print axioms smoothModel_formallySmooth
#print axioms algebraMap_X
#print axioms isSmoothAt_of_formallySmooth
#print axioms smoothAt_of_derivative_notMem

end LeanFormal.IUT.XiFPaper.Mzk1G1B1SmoothCriterionSubmActual
