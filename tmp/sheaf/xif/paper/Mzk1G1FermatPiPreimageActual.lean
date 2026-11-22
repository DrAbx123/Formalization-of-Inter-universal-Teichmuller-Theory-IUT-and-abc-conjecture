/-
G1-A: decomposing preimages of opens under the glued projection pi.

The two chart images cover Y_n, and on each chart the projection restricts to the chart map
(pi_ι0 / pi_ι1).  Hence the preimage of an open V under pi is the union of the two chart
images of the corresponding chart preimages.  This is the bookkeeping needed for
pi^{-1}(A^1_lambda) = U0 and pi^{-1}(A^1_t) = U1. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatPiActual
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open scoped AlgebraicGeometry
/-- The two chart images cover the glued Fermat curve. -/
theorem fermatCurve_cover (n : Nat) :
    (fermatChart0ToCurve n).opensRange ⊔ (fermatChartInfToCurve n).opensRange = ⊤ := by
  ext y
  constructor
  · intro _; exact trivial
  · intro _
    obtain ⟨i, x, rfl⟩ :=
      (Mzk1G1FermatTwoChartGluingActual.fermatTwoChartGlueData n).ι_jointly_surjective y
    cases i with
    | up i =>
      cases i
      · exact Or.inl ⟨x, rfl⟩
      · exact Or.inr ⟨x, rfl⟩
/-- The restriction of pi to the first chart. -/
theorem pi_apply_chart0 (n : Nat) (x : fermatChart0Scheme n) :
    pi n ((fermatChart0ToCurve n) x) = (piChart0 n) x := by
  rw [← Scheme.Hom.comp_apply, pi_ι0 n]
/-- The restriction of pi to the chart at infinity. -/
theorem pi_apply_chartInf (n : Nat) (x : fermatChartInfScheme n) :
    pi n ((fermatChartInfToCurve n) x) = (piChartInf n) x := by
  rw [← Scheme.Hom.comp_apply, pi_ι1 n]
/-- Preimages under pi decompose into the two chart preimages. -/
theorem pi_preimage_eq (n : Nat) (V : projectiveLineGlued.Opens) :
    (pi n) ⁻¹ᵁ V =
      (fermatChart0ToCurve n ''ᵁ ((piChart0 n) ⁻¹ᵁ V)) ⊔
        (fermatChartInfToCurve n ''ᵁ ((piChartInf n) ⁻¹ᵁ V)) := by
  ext y
  constructor
  · intro hy
    obtain ⟨i, x, rfl⟩ :=
      (Mzk1G1FermatTwoChartGluingActual.fermatTwoChartGlueData n).ι_jointly_surjective y
    cases i with
    | up i =>
      cases i
      · refine Or.inl ?_
        refine ⟨x, ?_, rfl⟩
        change (piChart0 n) x ∈ (V : Set projectiveLineGlued)
        rw [← pi_apply_chart0 n x]
        exact hy
      · refine Or.inr ?_
        refine ⟨x, ?_, rfl⟩
        change (piChartInf n) x ∈ (V : Set projectiveLineGlued)
        rw [← pi_apply_chartInf n x]
        exact hy
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · show (pi n) ((fermatChart0ToCurve n) x) ∈ V
      rw [pi_apply_chart0 n x]
      exact hx
    · show (pi n) ((fermatChartInfToCurve n) x) ∈ V
      rw [pi_apply_chartInf n x]
      exact hx
#print axioms fermatCurve_cover
#print axioms pi_preimage_eq
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageActual
