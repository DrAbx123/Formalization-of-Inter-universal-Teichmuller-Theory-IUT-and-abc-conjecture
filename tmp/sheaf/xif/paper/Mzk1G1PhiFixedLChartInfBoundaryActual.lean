/-
# B1 (emmy lane): the t-chart (qPiece piece) scheme-value dictionary

This file is the dual of Mzk1G1PhiFixedLChart0BoundaryActual (the lambda-chart dictionary):
the second chart of P^1 carries the coordinate t, and the transition is t = lambda-inverse
(chartMorphism_transition, Mzk1G1ProjectiveLineTransitionActual).  The three Belyi points read
on the t-chart are

* p1Zero (lambda = 0, t = infinity): never hit by a t-chart point
  (chartMorphismInf_not_mem_p1Zero, Mzk1G1PsiP1ZeroJudgeActual);
* p1One (lambda = 1, equivalently t = 1): hit iff t - 1 vanishes at the prime;
* p1Infinity (t = 0): hit iff t vanishes at the prime.

So, exactly as on the lambda-chart,

    chartMorphismInf a p is in boundarySetGlued  <->  a is in p  or  a - 1 is in p

(chartMorphismInf_mem_boundarySetGlued_iff).  The two chart judges are
chartMorphismInf_mem_p1One_iff / chartMorphismInf_mem_p1Infinity_iff; the key point is that
p1One and p1Infinity are SINGLE points (p1One_eq_singleton, p1Infinity_eq_singleton, from
chartPrime_eq_of_mem: any prime of Q[s] containing X - C c is the maximal ideal (X - C c)),
and that the point lambda = 1 of P^1 is ALSO a t-chart point:
localChart0 (chartPrime 1) = localChartInf (chartPrime 1), because the inverse of 1 is 1
(donor: Mzk1G1PhiFiberFiniteActual.exists_chartInf_of_chart0).  No overlap prime has to be
constructed, and no localization prime has to be lifted.

## What is proved (unconditional, no sorry/axiom)

1. chartMorphismInf_apply: point formula chartMorphismInf a p = localChartInf (comap (evalAt a) p).
2. p1One_eq_singleton, p1Infinity_eq_singleton: the two boundary points are singletons.
3. localChart0_chartPrime_one_eq_localChartInf: the lambda = 1 point is the t = 1 point.
4. chartMorphismInf_mem_p1One_iff, chartMorphismInf_mem_p1Infinity_iff: the chart judges.
5. chartMorphismInf_mem_boundarySetGlued_iff: THE T-CHART DICTIONARY (task declaration 1).
6. chartMorphismInf_point_notMem_boundary_iff: its AvoidsBoundary (ring) form.
7. psiFixed_qPiece_mem_boundary_iff / psiFixed_qPiece_notMem_boundary_iff: the dictionary
   instantiated at the actual second piece qPiece of Y_n (via psiFixed_qPiece_apply), i.e. the
   scheme-value bridge ON THE SCHEMES.
8. chartMorphismInf_comp_hPoly (t-chart formula of hPoly, t maps to h(t)) and
   psiFixed_comp_hPoly_qPiece_point_eq / _mem_boundary_iff: the dictionary for the composite
   psiFixed >> hPoly.

## CORRECTION to the task's declaration 2 (read before consuming)

The requested statement

  phiFixedL n T h hh ((qPiece n T).base P) = chartMorphismInf (evalAt (psiChartInfCoord n T) h) P

is FALSE, so it is NOT stated here (and nothing weaker is smuggled in under that name).
Reason, from the proven chart formulas in the tree:

* hPoly acts on the t-chart by t maps to h(t) (Mzk1G1PsiHPolyFinalActual.hPoly_ι_c0) and on the
  lambda-chart by lambda maps to lambda^d / hRev(lambda) (hPolyLam, hPoly_ι_c2);
* phiFixedL = psiFixed >> hPolyL with hPolyL = p1Inv >> hPoly >> p1Inv
  (Mzk1G1PsiHPolyLambdaActual.hPolyL_def), so hPolyL acts on the lambda-chart by
  lambda maps to h(lambda) (hPolyL_lambda_chart, proven) and hence on the t-chart by
  T maps to 1 / h(1/T);
* psiFixed sends qPiece to the t-chart point with t = psiChartInfCoord (psiFixed_qPiece_apply).
  Composing: on qPiece, phiFixedL is the point of P^1 with LAMBDA' = h(1/psiChartInfCoord)
  (equivalently t' = v^d / hRev(v) with v = psiChartInfCoord), NOT the t-chart point
  t' = h(v).  Since psiChartInfCoord = q-inverse times r^|T|, the value 1/v = q r^-|T| is in
  general not a regular function on qPiece = D(q), so phiFixedL restricted to qPiece is not of
  the form chartMorphismInf (polynomial in v) at all.
  Counterexample to the requested form: h = 1 + X (hh holds), T = {0} (then q = 1, v = r);
  at a point with r = 1 the true image has lambda' = 1 + 1 = 2, while the requested
  chartMorphismInf (evalAt v h) would give t' = 1 + 1 = 2, i.e. lambda' = 1/2.

What IS true and is proved here instead: on qPiece the composite keeps hPolyL
(phiFixedL_chartInf_point_apply), the t-chart dictionary of hPoly itself is
chartMorphismInf_comp_hPoly, and the t-chart dictionary of psiFixed is
psiFixed_qPiece_mem_boundary_iff.  For the hpsi gap the honest route is therefore: on the
chart0 piece use the lambda dictionary of Mzk1G1PhiFixedLChart0BoundaryActual; on qPiece use
p1Inv (which permutes {0,1,infinity}) to transport to the hPoly form above, or restrict to the
overlap where 1/v = q r^-|T| is regular.  This file supplies the t-chart dictionary and the
hPoly piece needed by both routes.

No sorry, no admit, no new axioms.
-/
import tmp.sheaf.xif.paper.Mzk1G1PhiFixedLChart0BoundaryActual
import tmp.sheaf.xif.paper.Mzk1G1PsiFixedTChartActual
import tmp.sheaf.xif.paper.Mzk1G1PhiFiberFiniteActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyLambdaPhiActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyLambdaFactsActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1600000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLChartInfBoundaryActual

open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1ZeroJudgeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedTChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PhiFiberFiniteActual

/-! ## 1. Point formula of the t-chart morphism -/

/-- The point of P^1 attached to p by the t-chart morphism: the t-chart point whose coordinate
is a (equivalently, the prime comap (evalAt a) p of Q[t]). -/
theorem chartMorphismInf_apply {R : Type} [CommRing R] [Algebra ℚ R] (a : R)
    (p : PrimeSpectrum R) :
    chartMorphismInf a p = localChartInf.base (PrimeSpectrum.comap (evalAt a) p) := by
  show (Spec.map (CommRingCat.ofHom (evalAt a)) ≫ localChartInf).base p = _
  simp only [Scheme.Hom.comp_apply, Spec.map_apply, CommRingCat.hom_ofHom]

/-! ## 2. The two t-chart boundary points are singletons -/

/-- p1One (lambda = 1) is the single point localChart0 (chartPrime 1): any prime of Q[s]
containing s - 1 is the maximal ideal (s - 1). -/
theorem p1One_eq_singleton :
    p1One = {localChart0.base (chartPrime 1)} := by
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    rw [p1One] at hz
    obtain ⟨q, hq, rfl⟩ := hz
    simp only [chartPoint] at hq
    rw [chartPrime_eq_of_mem 1 q hq]
    exact Set.mem_singleton _
  · intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact ⟨chartPrime 1, chartPrime_mem 1, rfl⟩

/-- p1Infinity (t = 0) is the single point localChartInf (chartPrime 0). -/
theorem p1Infinity_eq_singleton :
    p1Infinity = {localChartInf.base (chartPrime 0)} := by
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    rw [p1Infinity] at hz
    obtain ⟨q, hq, rfl⟩ := hz
    simp only [chartPoint] at hq
    rw [chartPrime_eq_of_mem 0 q hq]
    exact Set.mem_singleton _
  · intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact ⟨chartPrime 0, chartPrime_mem 0, rfl⟩

/-- The lambda = 1 point of P^1 is the t = 1 point: the inverse of 1 is 1, so the lambda-chart
point chartPrime 1 and the t-chart point chartPrime 1 coincide in P^1 (donor:
exists_chartInf_of_chart0). -/
theorem localChart0_chartPrime_one_eq_localChartInf :
    localChart0.base (chartPrime 1) = localChartInf.base (chartPrime 1) := by
  obtain ⟨y, hy, hq⟩ := exists_chartInf_of_chart0 (chartPrime 1) (chartPrime_mem 1)
  rw [chartPrime_eq_of_mem 1 y hy] at hq
  exact hq

/-! ## 3. The t-chart judges -/

/-- t-chart judge, lambda = infinity: a t-chart point has t = 0 (i.e. lies at lambda = infinity)
exactly when its coordinate vanishes at p. -/
theorem chartMorphismInf_mem_p1Infinity_iff {R : Type} [CommRing R] [Algebra ℚ R]
    (a : R) (p : PrimeSpectrum R) :
    chartMorphismInf a p ∈ p1Infinity ↔ a ∈ p.asIdeal := by
  have hinj : Function.Injective localChartInf.base := localChartInf.isOpenEmbedding.injective
  constructor
  · intro hmem
    rw [p1Infinity_eq_singleton, Set.mem_singleton_iff] at hmem
    have h1 : localChartInf.base (PrimeSpectrum.comap (evalAt a) p) =
        localChartInf.base (chartPrime 0) := by
      rw [← chartMorphismInf_apply a p, hmem]
    have h2 := hinj h1
    have h3 : Polynomial.X - Polynomial.C (0 : ℚ) ∈
        (PrimeSpectrum.comap (evalAt a) p).asIdeal := by
      rw [h2]
      exact chartPrime_mem 0
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h3
    have h4 : evalAt a (Polynomial.X - Polynomial.C (0 : ℚ)) = a := by
      rw [map_sub, evalAt_X, evalAt_C, map_zero, sub_zero]
    rwa [h4] at h3
  · intro ha
    rw [p1Infinity_eq_singleton, Set.mem_singleton_iff, chartMorphismInf_apply a p]
    have h2 : PrimeSpectrum.comap (evalAt a) p = chartPrime 0 := by
      apply chartPrime_eq_of_mem 0
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
      have h4 : evalAt a (Polynomial.X - Polynomial.C (0 : ℚ)) = a := by
        rw [map_sub, evalAt_X, evalAt_C, map_zero, sub_zero]
      rw [h4]
      exact ha
    rw [h2]

/-- t-chart judge, lambda = 1: a t-chart point is the point 1 of P^1 (lambda = 1 iff t = 1)
exactly when its coordinate equals 1 at p.  Both directions only use that p1One is the single
point localChart0 (chartPrime 1) and that this point is also the t-chart point chartPrime 1. -/
theorem chartMorphismInf_mem_p1One_iff {R : Type} [CommRing R] [Algebra ℚ R]
    (a : R) (p : PrimeSpectrum R) :
    chartMorphismInf a p ∈ p1One ↔ a - 1 ∈ p.asIdeal := by
  have hinj : Function.Injective localChartInf.base := localChartInf.isOpenEmbedding.injective
  constructor
  · intro hmem
    rw [p1One_eq_singleton, Set.mem_singleton_iff] at hmem
    have h1 : localChartInf.base (PrimeSpectrum.comap (evalAt a) p) =
        localChartInf.base (chartPrime 1) := by
      rw [← chartMorphismInf_apply a p, hmem]
      exact localChart0_chartPrime_one_eq_localChartInf
    have h2 := hinj h1
    have h3 : Polynomial.X - Polynomial.C (1 : ℚ) ∈
        (PrimeSpectrum.comap (evalAt a) p).asIdeal := by
      rw [h2]
      exact chartPrime_mem 1
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h3
    have h4 : evalAt a (Polynomial.X - Polynomial.C (1 : ℚ)) = a - 1 := by
      rw [map_sub, evalAt_X, evalAt_C, map_one]
    rwa [h4] at h3
  · intro ha
    rw [p1One_eq_singleton, Set.mem_singleton_iff, chartMorphismInf_apply a p]
    have h2 : PrimeSpectrum.comap (evalAt a) p = chartPrime 1 := by
      apply chartPrime_eq_of_mem 1
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
      have h4 : evalAt a (Polynomial.X - Polynomial.C (1 : ℚ)) = a - 1 := by
        rw [map_sub, evalAt_X, evalAt_C, map_one]
      rw [h4]
      exact ha
    rw [h2, localChart0_chartPrime_one_eq_localChartInf]

/-! ## 4. The t-chart boundary dictionary (dual of the lambda-chart one) -/

/-- t-chart boundary dictionary.  A t-chart point of P^1 with coordinate a lies on the Belyi
boundary {0, 1, infinity} exactly when a vanishes or equals 1 at p: the point lambda = 0 is
never a t-chart point (chartMorphismInf_not_mem_p1Zero), and the lambda = 1 / lambda = infinity
slots are read off by the two judges.  Exact dual of chartMorphism0_mem_boundarySetGlued_iff. -/
theorem chartMorphismInf_mem_boundarySetGlued_iff {R : Type} [CommRing R] [Algebra ℚ R]
    (a : R) (p : PrimeSpectrum R) :
    chartMorphismInf a p ∈ boundarySetGlued ↔ (a ∈ p.asIdeal ∨ a - 1 ∈ p.asIdeal) := by
  simp only [boundarySetGlued, Set.mem_union, chartMorphismInf_mem_p1Infinity_iff,
    chartMorphismInf_mem_p1One_iff]
  constructor
  · rintro ((h | h) | h)
    · exact absurd h (chartMorphismInf_not_mem_p1Zero (R := R) a p)
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)

/-- t-chart avoidance dictionary: a t-chart point avoids {0, 1, infinity} exactly when both a
and a - 1 are nonzero at p.  Ring-level form of the AvoidsBoundary obligations, dual to
phiFixedL_chart0_point_notMem_boundary_iff. -/
theorem chartMorphismInf_point_notMem_boundary_iff {R : Type} [CommRing R] [Algebra ℚ R]
    (a : R) (p : PrimeSpectrum R) :
    chartMorphismInf a p ∉ boundarySetGlued ↔ (a ∉ p.asIdeal ∧ a - 1 ∉ p.asIdeal) := by
  rw [chartMorphismInf_mem_boundarySetGlued_iff, not_or]

/-! ## 5. The dictionary on the schemes: the second piece qPiece of Y_n -/

/-- The t-chart dictionary on qPiece: a point of the second piece of Y_n is sent by psiFixed
into {0, 1, infinity} exactly when the chart coordinate v is 0 or 1 there.  (psiFixed sends
qPiece to the t-chart point t = v, psiFixed_qPiece_apply.) -/
theorem psiFixed_qPiece_mem_boundary_iff (n : Nat) (T : Finset ℚ)
    (P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T))) :
    (psiFixed n T).base ((qPiece n T).base P) ∈ boundarySetGlued ↔
      (psiChartInfCoord n T ∈ P.asIdeal ∨ psiChartInfCoord n T - 1 ∈ P.asIdeal) := by
  rw [psiFixed_qPiece_apply n T P]
  exact chartMorphismInf_mem_boundarySetGlued_iff _ P

/-- Avoidance on qPiece (ring form): a point of the second piece of Y_n avoids the Belyi
boundary under psiFixed exactly when v and v - 1 are nonzero there. -/
theorem psiFixed_qPiece_notMem_boundary_iff (n : Nat) (T : Finset ℚ)
    (P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T))) :
    (psiFixed n T).base ((qPiece n T).base P) ∉ boundarySetGlued ↔
      (psiChartInfCoord n T ∉ P.asIdeal ∧ psiChartInfCoord n T - 1 ∉ P.asIdeal) := by
  rw [psiFixed_qPiece_mem_boundary_iff, not_or]

/-! ## 6. The t-chart formula of hPoly (t maps to h(t)) and the composite psiFixed then hPoly

phiFixedL = psiFixed >> hPolyL is NOT a chart morphism on qPiece (see the header); the t-chart
morphism that IS exact is the one for hPoly itself, which is what the p1Inv conjugation of
hPolyL consumes. -/

/-- t-chart formula of hPoly: on the t-chart, hPoly is t maps to h(t) (donors: hPoly_ι_c0,
specMap_chartMorphismInf). -/
theorem chartMorphismInf_comp_hPoly {R : Type} [CommRing R] [Algebra ℚ R] (a : R)
    (h : Polynomial ℚ) (hh : h ≠ 0) :
    chartMorphismInf (R := R) a ≫ hPoly h hh = chartMorphismInf (R := R) (evalAt a h) := by
  show (Spec.map (CommRingCat.ofHom (evalAt a)) ≫ localChartInf) ≫ hPoly h hh = _
  rw [Category.assoc,
    show localChartInf ≫ hPoly h hh = chartMorphismInf (R := Polynomial ℚ) h from by
      rw [show localChartInf = (hPolyCover h hh).f HIdx.c0 from rfl]
      exact hPoly_ι_c0 h hh]
  exact specMap_chartMorphismInf (R := Polynomial ℚ) (S := R) (evalAt a)
    (by exact RingHom.ext_rat _ _) h

/-- The t-chart point formula of psiFixed then hPoly on qPiece: the composite is the t-chart
point of coordinate h(v), v = psiChartInfCoord.  (This is the TRUE statement of the shape
requested for phiFixedL; for phiFixedL = psiFixed then hPolyL the coordinate would be
1 / h(1/v), see the file header.) -/
theorem psiFixed_comp_hPoly_qPiece_point_eq (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T))) :
    ((psiFixed n T) ≫ hPoly h hh).base ((qPiece n T).base P) =
      (chartMorphismInf (R := Localization.Away (psiChartInfDenom n T))
        (evalAt (psiChartInfCoord n T) h)).base P := by
  have hι0 : qPiece n T ≫ psiFixed n T =
      chartMorphismInf (R := Localization.Away (psiChartInfDenom n T))
        (psiChartInfCoord n T) := psiFixed_ι_true n T
  have hι : qPiece n T ≫ ((psiFixed n T) ≫ hPoly h hh) =
      chartMorphismInf (R := Localization.Away (psiChartInfDenom n T))
        (psiChartInfCoord n T) ≫ hPoly h hh := by
    rw [← Category.assoc, hι0]
  calc ((psiFixed n T) ≫ hPoly h hh).base ((qPiece n T).base P)
      = (qPiece n T ≫ ((psiFixed n T) ≫ hPoly h hh)).base P :=
        (Scheme.Hom.comp_apply (qPiece n T) ((psiFixed n T) ≫ hPoly h hh) P).symm
    _ = (chartMorphismInf (R := Localization.Away (psiChartInfDenom n T))
          (psiChartInfCoord n T) ≫ hPoly h hh).base P := by rw [hι]
    _ = (chartMorphismInf (R := Localization.Away (psiChartInfDenom n T))
          (evalAt (psiChartInfCoord n T) h)).base P := by
        rw [chartMorphismInf_comp_hPoly]

/-- Boundary dictionary for psiFixed then hPoly on qPiece: the image is in {0, 1, infinity}
exactly when h(v) is 0 or 1 at the prime. -/
theorem psiFixed_comp_hPoly_qPiece_mem_boundary_iff (n : Nat) (T : Finset ℚ)
    (h : Polynomial ℚ) (hh : h ≠ 0)
    (P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T))) :
    ((psiFixed n T) ≫ hPoly h hh).base ((qPiece n T).base P) ∈ boundarySetGlued ↔
      (evalAt (R := Localization.Away (psiChartInfDenom n T))
          (psiChartInfCoord n T) h ∈ P.asIdeal ∨
        evalAt (R := Localization.Away (psiChartInfDenom n T))
          (psiChartInfCoord n T) h - 1 ∈ P.asIdeal) := by
  rw [psiFixed_comp_hPoly_qPiece_point_eq n T h hh P]
  exact chartMorphismInf_mem_boundarySetGlued_iff _ P

/-- The actual content of phiFixedL on qPiece: the honest composite formula
(phiFixedL_ι_true at the point level).  There is no chart morphism of the form
chartMorphismInf (polynomial) for it, see the file header. -/
theorem phiFixedL_chartInf_point_apply (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ)
    (hh : h ≠ 0) (P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T))) :
    phiFixedL n T h hh ((qPiece n T).base P) =
      ((chartMorphismInf (R := Localization.Away (psiChartInfDenom n T))
        (psiChartInfCoord n T)) ≫ hPolyL h hh).base P := by
  have hι : qPiece n T ≫ phiFixedL n T h hh =
      chartMorphismInf (R := Localization.Away (psiChartInfDenom n T))
        (psiChartInfCoord n T) ≫ hPolyL h hh :=
    Mzk1G1PsiHPolyLambdaFactsActual.phiFixedL_ι_true n T h hh
  calc phiFixedL n T h hh ((qPiece n T).base P)
      = (qPiece n T ≫ phiFixedL n T h hh).base P :=
        (Scheme.Hom.comp_apply (qPiece n T) (phiFixedL n T h hh) P).symm
    _ = ((chartMorphismInf (R := Localization.Away (psiChartInfDenom n T))
          (psiChartInfCoord n T)) ≫ hPolyL h hh).base P := by rw [hι]

/-! ## Axiom checks -/

#print axioms chartMorphismInf_apply
#print axioms p1One_eq_singleton
#print axioms p1Infinity_eq_singleton
#print axioms localChart0_chartPrime_one_eq_localChartInf
#print axioms chartMorphismInf_mem_p1Infinity_iff
#print axioms chartMorphismInf_mem_p1One_iff
#print axioms chartMorphismInf_mem_boundarySetGlued_iff
#print axioms chartMorphismInf_point_notMem_boundary_iff
#print axioms psiFixed_qPiece_mem_boundary_iff
#print axioms psiFixed_qPiece_notMem_boundary_iff
#print axioms chartMorphismInf_comp_hPoly
#print axioms psiFixed_comp_hPoly_qPiece_point_eq
#print axioms psiFixed_comp_hPoly_qPiece_mem_boundary_iff
#print axioms phiFixedL_chartInf_point_apply

end LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLChartInfBoundaryActual
