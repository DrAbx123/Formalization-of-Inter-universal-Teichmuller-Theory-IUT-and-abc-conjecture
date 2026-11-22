import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineChartsActual
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import tmp.sheaf.xif.paper.Mzk1G1PsiChartInfCoverActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineChartMapsActual
open AlgebraicGeometry MvPolynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineChartsActual

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The homogeneous coordinate ring of P^1. -/
abbrev A2 : Type := MvPolynomial (Fin 2) ℚ

/-- The affine coordinate lambda = X1/X0 as a ring map Q[X0,X1] -> Q[lambda]. -/
noncomputable def lambdaMap : A2 →+* Polynomial ℚ :=
  MvPolynomial.eval₂Hom (algebraMap ℚ (Polynomial ℚ))
    (fun i : Fin 2 => if (i : ℕ) = 0 then 1 else Polynomial.X)

/-- The same ring map into the global sections of Spec Q[lambda]. -/
noncomputable def lambdaGlobal : A2 →+* Γ(Spec (CommRingCat.of (Polynomial ℚ)), ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℚ))).inv.hom).comp lambdaMap

/-- The irrelevant ideal maps onto the unit ideal (X0 is sent to 1). -/
theorem lambdaIrrelevant :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)).toIdeal.map
      lambdaGlobal = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h0 : (MvPolynomial.X (0 : Fin 2) : A2) ∈
      HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ) :=
    HomogeneousIdeal.mem_irrelevant_of_mem (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)
      (i := 1) (by norm_num) X0_mem_degree_one
  have hX0 : (MvPolynomial.X (0 : Fin 2) : A2) ∈
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)).toIdeal :=
    HomogeneousIdeal.mem_iff.mpr h0
  have hmem := Ideal.mem_map_of_mem lambdaGlobal hX0
  have hf0 : lambdaGlobal (MvPolynomial.X (0 : Fin 2)) = 1 := by
    simp [lambdaGlobal, lambdaMap, MvPolynomial.eval₂Hom_X']
  rwa [hf0] at hmem

/-- The affine lambda-chart of P^1: Spec Q[lambda] -> P^1, lambda |-> [1 : lambda]. -/
noncomputable def chart0OfPolynomial :
    Spec (CommRingCat.of (Polynomial ℚ)) ⟶ projectiveLine :=
  Proj.fromOfGlobalSections (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)
    (X := Spec (CommRingCat.of (Polynomial ℚ))) lambdaGlobal lambdaIrrelevant

/-- The lambda-chart lands in the open chart D_+(X0) of P^1. -/
theorem chart0OfPolynomial_preimage_chart0 :
    (chart0OfPolynomial) ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ) (MvPolynomial.X 0) =
      (Spec (CommRingCat.of (Polynomial ℚ))).basicOpen
        (lambdaGlobal (MvPolynomial.X (0 : Fin 2))) :=
  Proj.fromOfGlobalSections_preimage_basicOpen (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)
    (X := Spec (CommRingCat.of (Polynomial ℚ))) (f := lambdaGlobal) (hf := lambdaIrrelevant)
    Nat.one_pos X0_mem_degree_one

/-- The affine t-chart of P^1: Spec Q[t] -> P^1, t |-> [t : 1]. -/
noncomputable def tMap : A2 →+* Polynomial ℚ :=
  MvPolynomial.eval₂Hom (algebraMap ℚ (Polynomial ℚ))
    (fun i : Fin 2 => if (i : ℕ) = 0 then Polynomial.X else 1)

noncomputable def tGlobal : A2 →+* Γ(Spec (CommRingCat.of (Polynomial ℚ)), ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℚ))).inv.hom).comp tMap

theorem tIrrelevant :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)).toIdeal.map
      tGlobal = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h1 : (MvPolynomial.X (1 : Fin 2) : A2) ∈
      HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ) :=
    HomogeneousIdeal.mem_irrelevant_of_mem (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)
      (i := 1) (by norm_num) X1_mem_degree_one
  have hX1 : (MvPolynomial.X (1 : Fin 2) : A2) ∈
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)).toIdeal :=
    HomogeneousIdeal.mem_iff.mpr h1
  have hmem := Ideal.mem_map_of_mem tGlobal hX1
  have hf1 : tGlobal (MvPolynomial.X (1 : Fin 2)) = 1 := by
    simp [tGlobal, tMap, MvPolynomial.eval₂Hom_X']
  rwa [hf1] at hmem

/-- The affine t-chart of P^1: Spec Q[t] -> P^1, t |-> [t : 1]. -/
noncomputable def chart1OfPolynomial :
    Spec (CommRingCat.of (Polynomial ℚ)) ⟶ projectiveLine :=
  Proj.fromOfGlobalSections (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)
    (X := Spec (CommRingCat.of (Polynomial ℚ))) tGlobal tIrrelevant

/-- The t-chart lands in the open chart D_+(X1) of P^1. -/
theorem chart1OfPolynomial_preimage_chart1 :
    (chart1OfPolynomial) ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ) (MvPolynomial.X 1) =
      (Spec (CommRingCat.of (Polynomial ℚ))).basicOpen
        (tGlobal (MvPolynomial.X (1 : Fin 2))) :=
  Proj.fromOfGlobalSections_preimage_basicOpen (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)
    (X := Spec (CommRingCat.of (Polynomial ℚ))) (f := tGlobal) (hf := tIrrelevant)
    Nat.one_pos X1_mem_degree_one

#print axioms chart0OfPolynomial
#print axioms chart0OfPolynomial_preimage_chart0
#print axioms chart1OfPolynomial
#print axioms chart1OfPolynomial_preimage_chart1
end LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineChartMapsActual
