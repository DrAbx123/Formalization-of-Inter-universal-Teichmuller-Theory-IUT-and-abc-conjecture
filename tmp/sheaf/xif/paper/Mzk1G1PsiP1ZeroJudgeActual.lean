import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineBoundaryActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineTransitionActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineChartPreimageActual
import Mathlib.Tactic

/-!
# Judging the boundary point p1Zero (lambda = 0)

Toolkit for p1Zero used by the psiFixed / B1 assembly.  localChart0 = p1GlueData.iota false is
an open immersion, hence injective on points (IsOpenEmbedding.injective).
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1ZeroJudgeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual

variable {R : Type} [CommRing R] [Algebra ℚ R]

/-- The chart0 point of a prime containing a lies at lambda = 0. -/
theorem chartMorphism0_mem_p1Zero_of_mem (a : R) (p : PrimeSpectrum R)
    (ha : a ∈ p.asIdeal) : chartMorphism0 a p ∈ p1Zero := by
  refine ⟨(Spec.map (CommRingCat.ofHom (evalAt a))).base p, ?_, rfl⟩
  show Polynomial.X - Polynomial.C (0 : ℚ) ∈
    (((Spec.map (CommRingCat.ofHom (evalAt a))).base p) : PrimeSpectrum (Polynomial ℚ)).asIdeal
  have hbase : (((Spec.map (CommRingCat.ofHom (evalAt a))).base p) :
      PrimeSpectrum (Polynomial ℚ)) = PrimeSpectrum.comap (evalAt a) p := rfl
  rw [hbase, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  simpa [evalAt, Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_C] using ha

/-- The chart0 point of p lies at lambda = 0 exactly when a lies in p. -/
theorem chartMorphism0_mem_p1Zero_iff (a : R) (p : PrimeSpectrum R) :
    chartMorphism0 a p ∈ p1Zero ↔ a ∈ p.asIdeal := by
  constructor
  · rw [p1Zero]
    rintro ⟨q, hq, hqeq⟩
    have hbase : ((Spec.map (CommRingCat.ofHom (evalAt a))).base p :
        PrimeSpectrum (Polynomial ℚ)) = PrimeSpectrum.comap (evalAt a) p := rfl
    have hinj : Function.Injective localChart0.base :=
      (localChart0).isOpenEmbedding.injective
    have h : q = (Spec.map (CommRingCat.ofHom (evalAt a))).base p := by
      apply hinj
      rw [hqeq]
      rfl
    have hq' : Polynomial.X - Polynomial.C (0 : ℚ) ∈ q.asIdeal := by
      change Polynomial.X - Polynomial.C (0 : ℚ) ∈ q.asIdeal at hq
      exact hq
    rw [h] at hq'
    rw [hbase, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hq'
    simpa [evalAt, Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_C] using hq'
  · intro ha
    exact chartMorphism0_mem_p1Zero_of_mem a p ha

#print axioms chartMorphism0_mem_p1Zero_of_mem
#print axioms chartMorphism0_mem_p1Zero_iff

/-- The finite point of the t-chart is never the lambda = 0 point: a common point of the two
charts would lie in the overlap, where the coordinate lambda is a unit, impossible in a prime. -/
theorem chartMorphismInf_not_mem_p1Zero {R : Type} [CommRing R] [Algebra ℚ R] (a : R)
    (p : PrimeSpectrum R) :
    chartMorphismInf a p ∉ p1Zero := by
  intro hmem
  rw [p1Zero] at hmem
  obtain ⟨q, hq, hqeq⟩ := hmem
  have hqrange : localChart0.base q ∈ localChartInf.opensRange := by
    rw [hqeq]
    refine Scheme.Hom.mem_opensRange.mpr
      ⟨(Spec.map (CommRingCat.ofHom (evalAt a))).base p, ?_⟩
    rw [chartMorphismInf, Scheme.Hom.comp_apply]
  have hqmem : q ∈ localChart0 ⁻¹ᵁ localChartInf.opensRange := hqrange
  rw [Mzk1G1ProjectiveLineChartPreimageActual.localChart0_preimage_localChartInf] at hqmem
  obtain ⟨z, hz⟩ := Scheme.Hom.mem_opensRange.mp hqmem
  have hXq : Polynomial.X ∈ q.asIdeal := by
    change Polynomial.X - Polynomial.C (0 : ℚ) ∈ q.asIdeal at hq
    simpa using hq
  have hbase : overlapToChart0.base z =
      PrimeSpectrum.comap (algebraMap (Polynomial ℚ) OverlapRing) z := rfl
  have hqcomap : PrimeSpectrum.comap (algebraMap (Polynomial ℚ) OverlapRing) z = q :=
    hbase.symm.trans hz
  have hXcomap :
      Polynomial.X ∈
        (PrimeSpectrum.comap (algebraMap (Polynomial ℚ) OverlapRing) z).asIdeal := by
    rw [hqcomap]
    exact hXq
  have halg : algebraMap (Polynomial ℚ) OverlapRing Polynomial.X ∈ z.asIdeal := by
    have h := hXcomap
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h
    exact h
  have hunit : IsUnit (algebraMap (Polynomial ℚ) OverlapRing Polynomial.X) := by
    rw [show algebraMap (Polynomial ℚ) OverlapRing Polynomial.X = ovLambda from rfl]
    exact isUnit_iff_exists_inv.mpr ⟨invLambda, ovLambda_mul_invLambda⟩
  have htop : z.asIdeal = ⊤ :=
    Ideal.eq_top_of_isUnit_mem (I := z.asIdeal) halg hunit
  exact z.isPrime.ne_top htop

#print axioms chartMorphismInf_not_mem_p1Zero

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1ZeroJudgeActual