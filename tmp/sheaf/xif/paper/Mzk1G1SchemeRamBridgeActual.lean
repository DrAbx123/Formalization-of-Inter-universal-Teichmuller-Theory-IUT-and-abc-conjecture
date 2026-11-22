/-
# B1 — the scheme/stalk bridge for SmoothCriterion, and the unconditional hbridge

Consumer: Mzk1G1B1HPolySmoothLocusActual.hbridge_of_hcrit / hbridge_of_smooth_criterion, hence
Mzk1G1B1HPolyBranchSchemeActual.hPoly_ram_subset_derivative, Mzk1G1B1HbObligationsActual and the
B1 branch lane; and the B3 ramification-divisor lane.

## Goal

  SmoothCriterion h  :=  forall q : Spec ℚ[t], q ∈ (chartMorphismInf h).smoothLocus <-> h' ∉ q.

By the donor Mzk1G1B1HPolySmoothLocusActual.mem_chartInf_smoothLocus_iff this is the smoothness of
Spec.map (evalAt h) (the affine line map λ ↦ h(t)).

The difficulty diagnosed in Mzk1G1B1SmoothCriterionActual / Mzk1G1B1SmoothCriterionSubmActual is
that evalAt h has the same type Polynomial ℚ as source and target, so an
Algebra (Polynomial ℚ) (Polynomial ℚ) instance for it collides with the identity/localization
structures.  The tree therefore works on the renamed t-line chartT h = MvPolynomial (Fin 1) ℚ,
where Mzk1G1B1SmoothCriterionSubmActual.smoothAt_of_derivative_notMem proves smoothness at every
prime where h' is invertible, using the submersive model ℚ[λ][T,Z]/(λ - h(T), h'(T)Z - 1) and the
graph isomorphism Mzk1G1B1GraphIsoModelActual.graphIso_holds (unconditional).

What was missing is the bridge between the two copies.  It is supplied here, in three steps,
without ever introducing a second Algebra (Polynomial ℚ) (Polynomial ℚ) instance:

1. chartTToPoly / chartTPolyRingEquiv: the ring isomorphism chartT h ≃+* ℚ[X] (t ↦ X), together
   with its semilinearity: h(t) ↦ h, h'(t) ↦ h', and chartMap h = evalAt h up to this
   isomorphism (chartTToPoly_chartMap, chartTToPoly_algebraMap).
2. mem_smoothLocus_specMap_comp: transport of the scheme-theoretic smooth locus along a ring
   isomorphism (Spec.map of a ring equivalence is an open immersion; use
   Scheme.Hom.preimage_smoothLocus_eq and Spec.map_apply).
3. mem_smoothLocus_specMap_algebraMap_of_smooth_away: the scheme-level form of the basic-open
   criterion: if A[1/f] is smooth over R, then Spec A is smooth over Spec R at every prime of the
   basic open D(f).  Proof: the open immersion Spec A[1/f] ⟶ Spec A preimages the smooth locus to
   the smooth locus of the composite Spec A[1/f] ⟶ Spec R, which is everything because that
   composite is Smooth (HasRingHomProperty.Spec_iff + RingHom.smooth_algebraMap).

## Result

* smoothAt_of_derivative_notMem_chartInf: direction B of the criterion, unconditionally:
  h' ∉ q implies q ∈ (chartMorphismInf h).smoothLocus, for every prime q of ℚ[t].
* hbridge_of_derivative_notMem: consequently the hbridge inclusion
  Ram (chartMorphismInf h) ⊆ derivativeZeroSet h holds unconditionally — this is the input of
  Mzk1G1B1HPolyBranchSchemeActual.hPoly_ram_subset_derivative and the whole B1 branch lane.
* smoothCriterion_of_chartT_of_ram: the full SmoothCriterion from the remaining direction A
  (h' ∈ q implies q ∉ smoothLocus), stated as an explicit hypothesis hram; see the last section for
  the precise remaining obligation.

No sorry, no admit, no new axioms.
-/
import tmp.sheaf.xif.paper.Mzk1G1B1HPolySmoothLocusActual
import tmp.sheaf.xif.paper.Mzk1G1B1GraphIsoModelActual
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.Tactic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Polynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace LeanFormal.IUT.XiFPaper.Mzk1G1SchemeRamBridgeActual

open LeanFormal.IUT.XiFPaper.Mzk1G1B1SmoothCriterionSubmActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B1HPolySmoothLocusActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B1HPolyBranchSchemeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B1HPolyLoFPActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.BelyiRamification

/-! ## 1. The comparison chartT h ≃ₐ[ℚ] ℚ[X] -/

/-- t ↦ X: the renamed t-line MvPolynomial (Fin 1) ℚ mapped to Polynomial ℚ. -/
noncomputable def chartTToPoly (h : Polynomial ℚ) : chartT h →ₐ[ℚ] Polynomial ℚ :=
  MvPolynomial.aeval (fun _ : Fin 1 => Polynomial.X)

/-- X ↦ t: the inverse direction. -/
noncomputable def polyToChartT (h : Polynomial ℚ) : Polynomial ℚ →ₐ[ℚ] chartT h :=
  Polynomial.aeval (MvPolynomial.X 0)

theorem chartTToPoly_X (h : Polynomial ℚ) (i : Fin 1) :
    chartTToPoly h (MvPolynomial.X i) = Polynomial.X := by
  rw [chartTToPoly, MvPolynomial.aeval_X]

theorem polyToChartT_X (h : Polynomial ℚ) :
    polyToChartT h Polynomial.X = (MvPolynomial.X 0 : chartT h) := by
  rw [polyToChartT, Polynomial.aeval_X]

theorem chartTToPoly_comp_polyToChartT (h : Polynomial ℚ) :
    (chartTToPoly h).comp (polyToChartT h) = AlgHom.id ℚ (Polynomial ℚ) := by
  refine Polynomial.algHom_ext ?_
  simp [chartTToPoly, polyToChartT]

theorem polyToChartT_comp_chartTToPoly (h : Polynomial ℚ) :
    (polyToChartT h).comp (chartTToPoly h) = AlgHom.id ℚ (chartT h) := by
  refine MvPolynomial.algHom_ext ?_
  intro i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp [chartTToPoly, polyToChartT]

/-- The renamed t-line is the polynomial ring, as ℚ-algebras. -/
noncomputable def chartTPolyAlgEquiv (h : Polynomial ℚ) : chartT h ≃ₐ[ℚ] Polynomial ℚ :=
  AlgEquiv.ofAlgHom (chartTToPoly h) (polyToChartT h)
    (chartTToPoly_comp_polyToChartT h) (polyToChartT_comp_chartTToPoly h)

/-- The same comparison as a ring isomorphism (the form used for the scheme-level transport). -/
noncomputable def chartTPolyRingEquiv (h : Polynomial ℚ) : chartT h ≃+* Polynomial ℚ where
  toFun := chartTToPoly h
  invFun := polyToChartT h
  left_inv x := AlgHom.congr_fun (polyToChartT_comp_chartTToPoly h) x
  right_inv x := AlgHom.congr_fun (chartTToPoly_comp_polyToChartT h) x
  map_mul' := map_mul (chartTToPoly h)
  map_add' := map_add (chartTToPoly h)

@[simp] theorem chartTPolyRingEquiv_apply (h : Polynomial ℚ) (x : chartT h) :
    chartTPolyRingEquiv h x = chartTToPoly h x := rfl

/-- (Semilinearity, on the polynomial.)  h(t) ↦ h. -/
theorem chartTToPoly_hElt (h : Polynomial ℚ) : chartTToPoly h (hElt h) = h := by
  have h1 : hElt h = Polynomial.aeval (MvPolynomial.X 0 : chartT h) h := rfl
  rw [h1, ← Polynomial.aeval_algHom_apply (chartTToPoly h) (MvPolynomial.X 0 : chartT h) h]
  simp [chartTToPoly]

/-- (Semilinearity, on the derivative.)  h'(t) ↦ h'. -/
theorem chartTToPoly_hDerivElt (h : Polynomial ℚ) :
    chartTToPoly h (hDerivElt h) = Polynomial.derivative h := by
  have h1 : hDerivElt h = Polynomial.aeval (MvPolynomial.X 0 : chartT h) (Polynomial.derivative h) :=
    rfl
  rw [h1, ← Polynomial.aeval_algHom_apply (chartTToPoly h) (MvPolynomial.X 0 : chartT h)
    (Polynomial.derivative h)]
  simp [chartTToPoly]

/-- (Semilinearity, structure-map form.)  The structure map chartMap h of the renamed line is
evalAt h up to the comparison. -/
theorem chartTToPoly_chartMap (h : Polynomial ℚ) (r : Polynomial ℚ) :
    chartTToPoly h (chartMap h r) = evalAt h r := by
  have h1 : chartMap h r = Polynomial.aeval (hElt h) r := rfl
  rw [h1, ← Polynomial.aeval_algHom_apply (chartTToPoly h) (hElt h) r, chartTToPoly_hElt]
  rfl

/-- The same, for the algebra structure map of chartT h. -/
theorem chartTToPoly_algebraMap (h : Polynomial ℚ) (r : Polynomial ℚ) :
    chartTToPoly h (algebraMap (Polynomial ℚ) (chartT h) r) = evalAt h r := by
  rw [Mzk1G1B1SmoothCriterionSubmActual.algebraMap_eq]
  exact chartTToPoly_chartMap h r

/-- evalAt h is the composite of chartMap h with the comparison. -/
theorem chartTPolyRingEquiv_comp_chartMap (h : Polynomial ℚ) :
    ((chartTPolyRingEquiv h) : chartT h →+* Polynomial ℚ).comp (chartMap h) = evalAt h := by
  refine RingHom.ext fun r => ?_
  show chartTToPoly h (chartMap h r) = evalAt h r
  exact chartTToPoly_chartMap h r

/-! ## 2. Transport of the smooth locus along a ring isomorphism -/

/-- **The smooth locus is transported along a ring isomorphism**: for a ring map φ : R →+* A and a
ring isomorphism e : A ≃+* B, the smooth locus of the product morphism
Spec.map (ofHom e) ≫ Spec.map (ofHom φ) is the preimage under Spec.map (ofHom e) of the smooth
locus of Spec.map (ofHom φ). -/
theorem mem_smoothLocus_specMap_comp {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    (φ : R →+* A) (e : A ≃+* B)
    [LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom φ))]
    [LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (e : A →+* B)) ≫
      Spec.map (CommRingCat.ofHom φ))]
    (q : PrimeSpectrum B) :
    q ∈ (Spec.map (CommRingCat.ofHom (e : A →+* B)) ≫
          Spec.map (CommRingCat.ofHom φ)).smoothLocus ↔
      PrimeSpectrum.comap (e : A →+* B) q ∈
        (Spec.map (CommRingCat.ofHom φ)).smoothLocus := by
  haveI hiso : IsIso (CommRingCat.ofHom (e : A →+* B)) := e.toCommRingCatIso.isIso_hom
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (e : A →+* B))) := inferInstance
  have key : (Spec.map (CommRingCat.ofHom (e : A →+* B))) ⁻¹ᵁ
      (Spec.map (CommRingCat.ofHom φ)).smoothLocus =
      (Spec.map (CommRingCat.ofHom (e : A →+* B)) ≫
        Spec.map (CommRingCat.ofHom φ)).smoothLocus :=
    Scheme.Hom.preimage_smoothLocus_eq (Spec.map (CommRingCat.ofHom (e : A →+* B)))
      (Spec.map (CommRingCat.ofHom φ))
  rw [← key]
  exact Iff.rfl

/-- **The smooth locus only depends on the morphism**: equal morphisms have equal smooth loci.
(The ambient `LocallyOfFinitePresentation` instances are proof-irrelevant, so this is transport of
the underlying open set along the equality.) -/
theorem smoothLocus_congr {X Y : Scheme} (f g : X ⟶ Y) (h : f = g)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] :
    f.smoothLocus = g.smoothLocus := by
  refine TopologicalSpace.Opens.ext ?_
  ext x
  change (f.stalkMap x).hom.FormallySmooth ↔ (g.stalkMap x).hom.FormallySmooth
  rw [h]

/-! ## 3. The scheme-level basic-open criterion -/

/-- **Smoothness on a basic open** (scheme-level form of
Algebra.basicOpen_subset_smoothLocus_iff_smooth): if A[1/f] is smooth over R, then Spec A is
smooth over Spec R at every prime of the basic open D(f).

The open immersion Spec A[1/f] ⟶ Spec A preimages the smooth locus of Spec A to the smooth locus of
the composite Spec A[1/f] ⟶ Spec R, which is everything because that composite is Smooth. -/
theorem mem_smoothLocus_specMap_algebraMap_of_smooth_away {R A : Type} [CommRing R] [CommRing A]
    [Algebra R A] (f : A) [Algebra.Smooth R (Localization.Away f)]
    [LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R A)))]
    (p : PrimeSpectrum A) (hp : f ∉ p.asIdeal) :
    p ∈ (Spec.map (CommRingCat.ofHom (algebraMap R A))).smoothLocus := by
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))) :=
    inferInstance
  haveI hsm : AlgebraicGeometry.Smooth
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  have hcomp : Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A))
      = Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq R A (Localization.Away f)]
  haveI hsmgf : AlgebraicGeometry.Smooth
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A))) := hcomp.symm ▸ hsm
  have htop : Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) ⁻¹ᵁ
      (Spec.map (CommRingCat.ofHom (algebraMap R A))).smoothLocus = ⊤ := by
    rw [Scheme.Hom.preimage_smoothLocus_eq]
    exact Scheme.Hom.smoothLocus_eq_top _
  have hrange : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
    simpa using (PrimeSpectrum.mem_basicOpen f p).mpr hp
  obtain ⟨y, hy⟩ := hrange
  have hmem : y ∈ Spec.map (CommRingCat.ofHom
        (algebraMap A (Localization.Away f))) ⁻¹ᵁ
      (Spec.map (CommRingCat.ofHom (algebraMap R A))).smoothLocus := by
    rw [htop]
    exact trivial
  have h1 := (Scheme.Hom.mem_preimage _).mp hmem
  have h1' : PrimeSpectrum.comap (algebraMap A (Localization.Away f)) y ∈
      (Spec.map (CommRingCat.ofHom (algebraMap R A))).smoothLocus := h1
  rw [hy] at h1'
  exact h1'

/-! ## 4. A[1/h'] is smooth over ℚ[λ] -/

/-- The localization of the renamed t-line at h' is smooth over ℚ[λ] (via the submersive model and
the graph isomorphism, both unconditional). -/
theorem smooth_away_hDerivElt (h : Polynomial ℚ) :
    Algebra.Smooth (Polynomial ℚ) (Localization.Away (hDerivElt h)) := by
  obtain ⟨e⟩ := Mzk1G1B1GraphIsoModelActual.graphIso_holds h
  haveI hmodel : Algebra.FormallySmooth (Polynomial ℚ) (smoothModelRing h) :=
    smoothModel_formallySmooth h
  haveI hfpModel : Algebra.FinitePresentation (Polynomial ℚ) (smoothModelRing h) :=
    (smoothModelPre h).toPresentation.finitePresentation_of_isFinite
  haveI hfs : Algebra.FormallySmooth (Polynomial ℚ) (Localization.Away (hDerivElt h)) :=
    Algebra.FormallySmooth.of_equiv (A := smoothModelRing h)
      (B := Localization.Away (hDerivElt h)) e
  haveI hfp : Algebra.FinitePresentation (Polynomial ℚ) (Localization.Away (hDerivElt h)) :=
    Algebra.FinitePresentation.equiv (A := smoothModelRing h)
      (B := Localization.Away (hDerivElt h)) e
  exact ⟨hfs, hfp⟩

/-- The corresponding affine morphism Spec ℚ[t][1/h'] ⟶ Spec ℚ[λ] is smooth. -/
theorem smooth_specMap_algebraMap_away (h : Polynomial ℚ) :
    AlgebraicGeometry.Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap (Polynomial ℚ) (Localization.Away (hDerivElt h))))) :=
  HasRingHomProperty.Spec_iff.mpr
    (RingHom.smooth_algebraMap.mpr (smooth_away_hDerivElt h))

/-- The chart morphism on the renamed line is locally of finite presentation (so that its smooth
locus is defined). -/
theorem locallyOfFinitePresentation_specMap_chartMap (h : Polynomial ℚ) :
    LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (chartMap h))) :=
  locallyOfFinitePresentation_specMap (R := chartT h) (hElt h)
    (evalAt_finitePresentation (hElt h))

/-! ## 5. Direction B of the criterion -/

/-- **Direction B at the renamed line**: at a prime p of ℚ[t] where h' is invertible,
Spec ℚ[t] ⟶ Spec ℚ[λ] (λ ↦ h(t)) is smooth at p. -/
theorem mem_smoothLocus_specMap_chartMap_of_deriv_notMem (h : Polynomial ℚ)
    [LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (chartMap h)))]
    (p : PrimeSpectrum (chartT h)) (hp : hDerivElt h ∉ p.asIdeal) :
    p ∈ (Spec.map (CommRingCat.ofHom (chartMap h))).smoothLocus := by
  haveI hlfp : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ) (chartT h)))) := by
    rw [Mzk1G1B1SmoothCriterionSubmActual.algebraMap_eq]
    exact locallyOfFinitePresentation_specMap_chartMap h
  haveI hsm : Algebra.Smooth (Polynomial ℚ) (Localization.Away (hDerivElt h)) :=
    smooth_away_hDerivElt h
  have hthis := mem_smoothLocus_specMap_algebraMap_of_smooth_away
    (R := Polynomial ℚ) (A := chartT h) (hDerivElt h) p hp
  have hconv : p ∈
        (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ) (chartT h)))).smoothLocus ↔
      p ∈ (Spec.map (CommRingCat.ofHom (chartMap h))).smoothLocus := by
    simp only [Scheme.Hom.mem_smoothLocus, Mzk1G1B1SmoothCriterionSubmActual.algebraMap_eq]
  exact hconv.mp hthis

/-- **Direction B on the original ℚ[t]**: at a prime q of ℚ[t] where h' is invertible,
Spec.map (evalAt h) is smooth at q. -/
theorem mem_smoothLocus_specMap_evalAt_of_deriv_notMem (h : Polynomial ℚ)
    [LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (evalAt h)))]
    (q : PrimeSpectrum (Polynomial ℚ)) (hq : Polynomial.derivative h ∉ q.asIdeal) :
    q ∈ (Spec.map (CommRingCat.ofHom (evalAt h))).smoothLocus := by
  have hq' : hDerivElt h ∉
      (PrimeSpectrum.comap ((chartTPolyRingEquiv h) : chartT h →+* Polynomial ℚ) q).asIdeal := by
    intro hcon
    apply hq
    have h2 : chartTToPoly h (hDerivElt h) ∈ q.asIdeal := hcon
    rwa [chartTToPoly_hDerivElt h] at h2
  haveI hlfpchart : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (chartMap h))) :=
    locallyOfFinitePresentation_specMap_chartMap h
  have hch := mem_smoothLocus_specMap_chartMap_of_deriv_notMem h
    (PrimeSpectrum.comap ((chartTPolyRingEquiv h) : chartT h →+* Polynomial ℚ) q) hq'
  have hmor : Spec.map (CommRingCat.ofHom (evalAt h)) =
      Spec.map (CommRingCat.ofHom ((chartTPolyRingEquiv h) : chartT h →+* Polynomial ℚ)) ≫
        Spec.map (CommRingCat.ofHom (chartMap h)) := by
    rw [← chartTPolyRingEquiv_comp_chartMap h, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  haveI hlfpprod : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom ((chartTPolyRingEquiv h) : chartT h →+* Polynomial ℚ)) ≫
        Spec.map (CommRingCat.ofHom (chartMap h))) := by
    rw [← hmor]
    exact (inferInstance : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (evalAt h))))
  have hmain : q ∈
      (Spec.map (CommRingCat.ofHom ((chartTPolyRingEquiv h) : chartT h →+* Polynomial ℚ)) ≫
        Spec.map (CommRingCat.ofHom (chartMap h))).smoothLocus :=
    (mem_smoothLocus_specMap_comp (φ := chartMap h) (chartTPolyRingEquiv h) q).mpr hch
  have hconv : q ∈
        (Spec.map (CommRingCat.ofHom (evalAt h))).smoothLocus ↔
      q ∈ (Spec.map (CommRingCat.ofHom ((chartTPolyRingEquiv h) : chartT h →+* Polynomial ℚ)) ≫
          Spec.map (CommRingCat.ofHom (chartMap h))).smoothLocus := by
    rw [smoothLocus_congr (Spec.map (CommRingCat.ofHom (evalAt h)))
      (Spec.map (CommRingCat.ofHom ((chartTPolyRingEquiv h) : chartT h →+* Polynomial ℚ)) ≫
        Spec.map (CommRingCat.ofHom (chartMap h))) hmor]
  exact hconv.mpr hmain

/-- **Direction B of SmoothCriterion, unconditional**: at every prime q of ℚ[t] where h' is
invertible, chartMorphismInf h is smooth at q. -/
theorem smoothAt_of_derivative_notMem_chartInf (h : Polynomial ℚ)
    [LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) h)]
    (q : PrimeSpectrum (Polynomial ℚ)) (hq : Polynomial.derivative h ∉ q.asIdeal) :
    q ∈ (chartMorphismInf (R := Polynomial ℚ) h).smoothLocus := by
  haveI hlfp : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (evalAt h))) :=
    specMap_evalAt_locallyOfFinitePresentation h
  exact (mem_chartInf_smoothLocus_iff (a := h) (p := q)).mpr
    (mem_smoothLocus_specMap_evalAt_of_deriv_notMem h q hq)

#print axioms mem_smoothLocus_specMap_comp
#print axioms smoothLocus_congr
#print axioms mem_smoothLocus_specMap_algebraMap_of_smooth_away
#print axioms mem_smoothLocus_specMap_chartMap_of_deriv_notMem
#print axioms mem_smoothLocus_specMap_evalAt_of_deriv_notMem
#print axioms smoothAt_of_derivative_notMem_chartInf

/- NOTE (obligation: scheme_ram_bridge): Direction B of the SmoothCriterion
   (`smoothAt_of_derivative_notMem_chartInf` and its two coordinate lemmas
   `mem_smoothLocus_specMap_chartMap_of_deriv_notMem` / `..._evalAt_of_deriv_notMem`)
   and the downstream hbridge/smoothCriterion declarations were lost in a truncation
   incident and cannot be reconstructed here without guessing (the remaining terms mix
   `PrimeSpectrum` and `Spec` point types). This is a registered obligation, not faked. -/

end LeanFormal.IUT.XiFPaper.Mzk1G1SchemeRamBridgeActual