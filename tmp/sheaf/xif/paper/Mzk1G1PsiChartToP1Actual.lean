import tmp.sheaf.xif.paper.Mzk1G1PsiChartMapsActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineChartsActual
import tmp.sheaf.xif.paper.Mzk1G1FermatTwoChartGluingActual
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartToP1Actual
open AlgebraicGeometry MvPolynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineChartsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatTwoChartGluingActual

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : Nat) (T : Finset ℚ)

/-- The homogeneous coordinate ring of the target P^1. -/
abbrev A2 : Type := MvPolynomial (Fin 2) ℚ

/-- Evaluate Q[X0,X1] on the first Fermat chart by X0 -> u = prod (x - t) and X1 -> 1:
the resulting map of P^1 is the point [u : 1]. -/
noncomputable def psiChart0Eval : A2 →+* R n :=
  MvPolynomial.eval₂Hom (algebraMap ℚ (R n))
    (fun i : Fin 2 => if (i : ℕ) = 0 then psiChart0Coord n T else 1)

/-- The same ring map, seen as a map into the global sections of the affine chart U0. -/
noncomputable def psiChart0Global : A2 →+* Γ(fermatChart0Scheme n, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (R n))).inv.hom).comp (psiChart0Eval n T)

/-- X1 is sent to the constant 1, hence the irrelevant ideal maps onto the unit ideal:
the pair of global sections has no common zero. -/
theorem psiChart0Irrelevant :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)).toIdeal.map
      (psiChart0Global n T) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h1 : (MvPolynomial.X (1 : Fin 2) : A2) ∈
      HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ) :=
    HomogeneousIdeal.mem_irrelevant_of_mem (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)
      (i := 1) (by norm_num) X1_mem_degree_one
  have hX1 : (MvPolynomial.X (1 : Fin 2) : A2) ∈
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)).toIdeal :=
    HomogeneousIdeal.mem_iff.mpr h1
  have hmem := Ideal.mem_map_of_mem (psiChart0Global n T) hX1
  have hf1 : psiChart0Global n T (MvPolynomial.X (1 : Fin 2)) = 1 := by
    simp [psiChart0Global, psiChart0Eval, MvPolynomial.eval₂Hom_X']
  rwa [hf1] at hmem

/-- THE FIRST CHART OF psi AS AN ACTUAL SCHEME MORPHISM TO P^1: the affine Fermat chart
U0 = Spec A0 maps to P^1 by the homogeneous pair of sections ([u : 1]), u = prod (x - t). -/
noncomputable def psiChart0ToP1 : fermatChart0Scheme n ⟶ projectiveLine :=
  Proj.fromOfGlobalSections (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)
    (X := fermatChart0Scheme n) (psiChart0Global n T) (psiChart0Irrelevant n T)

/-- The zero-fiber statement: the preimage of the open chart D_+(X0) is exactly the basic
open D(u) = D(prod (x - t)) of the first chart, i.e. the complement of the protected
divisor D_T. -/
theorem psiChart0ToP1_preimage_basicOpen :
    (psiChart0ToP1 n T) ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ) (MvPolynomial.X 0) =
      (fermatChart0Scheme n).basicOpen (psiChart0Global n T (MvPolynomial.X 0)) :=
  Proj.fromOfGlobalSections_preimage_basicOpen (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)
    (X := fermatChart0Scheme n) (f := psiChart0Global n T) (hf := psiChart0Irrelevant n T)
    Nat.one_pos X0_mem_degree_one

#print axioms psiChart0Irrelevant
#print axioms psiChart0ToP1
#print axioms psiChart0ToP1_preimage_basicOpen
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartToP1Actual
