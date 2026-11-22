import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineBoundaryActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineTransitionActual
import Mathlib.Tactic
/-!
# Judging the boundary point p1One (lambda = 1)

Mirror of the `p1Zero` judgment lemmas of `Mzk1G1PsiP1ZeroJudgeActual`, with
`chartPoint 1` and `evalAt a (X - C 1) = a - 1`.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1OneJudgeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
variable {R : Type} [CommRing R] [Algebra ℚ R]

/-- The chart0 point of a prime containing `a - 1` lies at lambda = 1. -/
theorem chartMorphism0_mem_p1One_of_mem (a : R) (p : PrimeSpectrum R)
    (ha : a - 1 ∈ p.asIdeal) : chartMorphism0 a p ∈ p1One := by
  refine ⟨(Spec.map (CommRingCat.ofHom (evalAt a))).base p, ?_, rfl⟩
  show Polynomial.X - Polynomial.C (1 : ℚ) ∈
    (((Spec.map (CommRingCat.ofHom (evalAt a))).base p) : PrimeSpectrum (Polynomial ℚ)).asIdeal
  have hbase : (((Spec.map (CommRingCat.ofHom (evalAt a))).base p) :
      PrimeSpectrum (Polynomial ℚ)) = PrimeSpectrum.comap (evalAt a) p := rfl
  rw [hbase, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  have h1 : evalAt (R := R) a (Polynomial.X - Polynomial.C (1 : ℚ)) = a - 1 := by
    rw [map_sub, evalAt_X, evalAt_C, map_one]
  rw [h1]; exact ha

/-- Chart0 point membership in `p1One` is exactly `a - 1 ∈ p`. -/
theorem chartMorphism0_mem_p1One_iff (a : R) (p : PrimeSpectrum R) :
    chartMorphism0 a p ∈ p1One ↔ a - 1 ∈ p.asIdeal := by
  constructor
  · rw [p1One]
    rintro ⟨q, hq, hqeq⟩
    have hbase : (((Spec.map (CommRingCat.ofHom (evalAt a))).base p) :
        PrimeSpectrum (Polynomial ℚ)) = PrimeSpectrum.comap (evalAt a) p := rfl
    have hinj : Function.Injective localChart0.base := (localChart0).isOpenEmbedding.injective
    have h : q = (Spec.map (CommRingCat.ofHom (evalAt a))).base p := by
      apply hinj
      rw [hqeq]; rfl
    have hq' : Polynomial.X - Polynomial.C (1 : ℚ) ∈ q.asIdeal := by
      change Polynomial.X - Polynomial.C (1 : ℚ) ∈ q.asIdeal at hq
      exact hq
    rw [h] at hq'
    rw [hbase, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hq'
    have h1 : evalAt (R := R) a (Polynomial.X - Polynomial.C (1 : ℚ)) = a - 1 := by
      rw [map_sub, evalAt_X, evalAt_C, map_one]
    rwa [h1] at hq'
  · intro ha
    exact chartMorphism0_mem_p1One_of_mem a p ha

#print axioms chartMorphism0_mem_p1One_of_mem
#print axioms chartMorphism0_mem_p1One_iff
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1OneJudgeActual
end