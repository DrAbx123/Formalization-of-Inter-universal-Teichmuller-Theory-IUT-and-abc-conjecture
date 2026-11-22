import tmp.sheaf.xif.paper.S2812Torsion23Actual
import tmp.sheaf.xif.paper.S2809E6FiniteActual
import tmp.sheaf.xif.paper.S2803F6CompleteActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2790F6Actual
open LeanFormal.IUT.XiFPaper.S2809E6FiniteActual
open LeanFormal.IUT.XiFPaper.S2803F6CompleteActual
open WeierstrassCurve
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000
namespace LeanFormal.IUT.XiFPaper.S2816Torsion23ActualAdapted

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := ⟨gaussianPolynomial_irreducible⟩
local instance : DecidableEq (↥S2790F6) := Classical.decEq _
local instance : DecidableEq (AlgebraicClosure ↥S2790F6) := Classical.decEq _
local instance : IsAlgClosure S2790F6 S2790L :=
  { isAlgClosed := IsAlgClosure.isAlgClosed GaussianField
    isAlgebraic := inferInstance }

theorem S2816_torsion23 :
    PuncturedEllipticCurve.Torsion23Rational (S2790E.baseChange S2790F6) := by
  unfold PuncturedEllipticCurve.Torsion23Rational PuncturedEllipticCurve.AllNTorsionRational
  intro P hP
  let F6 := ↥S2790F6
  let L1 := AlgebraicClosure F6
  let e := S2812Equiv
  rcases P with _ | ⟨x, y, hns⟩
  · refine ⟨0, ?_⟩
    exact (Affine.Point.map (Algebra.ofId F6 L1)).map_zero
  · -- some case
    let W0 : Affine GaussianField := S2790E.curve.toAffine
    have hnsL : (W0.baseChange S2790L).Nonsingular (e x) (e y) := by
      have hmap : ((W0.baseChange F6).baseChange L1).map (e : L1 →+* S2790L) =
          W0.baseChange S2790L := by
        change WeierstrassCurve.map
          (WeierstrassCurve.map
            (WeierstrassCurve.map W0 (algebraMap GaussianField F6))
            (algebraMap F6 L1)) (e : L1 →+* S2790L) =
              WeierstrassCurve.map W0 (algebraMap GaussianField S2790L)
        rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
        have hcomp :
            ((e : L1 →+* S2790L).comp (algebraMap F6 L1)).comp
                (algebraMap GaussianField F6) =
              algebraMap GaussianField S2790L := by
          ext z
          simp only [RingHom.comp_apply]
          have h1 := e.commutes ((algebraMap GaussianField F6) z)
          have h2 := IsScalarTower.algebraMap_apply GaussianField F6 S2790L z
          simpa using h1.trans h2.symm
        rw [hcomp]
      have h := (WeierstrassCurve.Affine.map_nonsingular
        (W := (W0.baseChange F6).baseChange L1) (f := (e : L1 →+* S2790L)) e.injective x y).mpr hns
      simpa [hmap] using h
    let x0 : F6 := ⟨e x, ?_⟩
    let y0 : F6 := ⟨e y, ?_⟩
    · sorry
end LeanFormal.IUT.XiFPaper.S2816Torsion23ActualAdapted
end