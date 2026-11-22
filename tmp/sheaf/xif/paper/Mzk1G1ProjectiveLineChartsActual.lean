import tmp.sheaf.xif.paper.Mzk1G1FiniteDisjointBelyiActual
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.Tactic

set_option relaxedAutoImplicit false
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineChartsActual
open AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual projective line P^1 = Proj Q[X0,X1] (same object as the one used by the
G-K finite family file; shared object of the project). -/
noncomputable def projectiveLine : Scheme :=
  AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)

/-- The shared projective line is definitionally the one used by the G-K file. -/
theorem projectiveLine_eq_gk : projectiveLine =
    LeanFormal.IUT.XiFPaper.G1FiniteDisjointBelyiActual.projectiveLine := rfl

/-- The homogeneous coordinate ring of P^1. -/
abbrev p1Ring : Type := MvPolynomial (Fin 2) ℚ

/-- The homogeneous coordinate X0 has degree 1. -/
theorem X0_mem_degree_one :
    MvPolynomial.X (0 : Fin 2) ∈ MvPolynomial.homogeneousSubmodule (Fin 2) ℚ 1 := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact MvPolynomial.isHomogeneous_X (R := ℚ) 0

/-- The homogeneous coordinate X1 has degree 1. -/
theorem X1_mem_degree_one :
    MvPolynomial.X (1 : Fin 2) ∈ MvPolynomial.homogeneousSubmodule (Fin 2) ℚ 1 := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact MvPolynomial.isHomogeneous_X (R := ℚ) 1

/-- The actual chart 0 of P^1: the affine chart D_+(X0) = Spec (Q[X1/X0]) as an open
immersion into P^1, via the homogeneous localization at X0. -/
noncomputable def chart0 :
    Spec (CommRingCat.of
      (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)
        (MvPolynomial.X (0 : Fin 2)))) ⟶ projectiveLine :=
  Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ) (MvPolynomial.X (0 : Fin 2))
    X0_mem_degree_one Nat.one_pos

/-- The actual chart 1 of P^1: the affine chart D_+(X1) = Spec (Q[X0/X1]). -/
noncomputable def chart1 :
    Spec (CommRingCat.of
      (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)
        (MvPolynomial.X (1 : Fin 2)))) ⟶ projectiveLine :=
  Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ) (MvPolynomial.X (1 : Fin 2))
    X1_mem_degree_one Nat.one_pos

/-- Both charts of P^1 are open immersions. -/
instance : IsOpenImmersion (chart0) :=
  inferInstanceAs (IsOpenImmersion
    (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ) (MvPolynomial.X (0 : Fin 2))
      X0_mem_degree_one Nat.one_pos))

instance : IsOpenImmersion (chart1) :=
  inferInstanceAs (IsOpenImmersion
    (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ) (MvPolynomial.X (1 : Fin 2))
      X1_mem_degree_one Nat.one_pos))


/-- The product X0 * X1 is homogeneous of degree 2. -/
theorem X0_mul_X1_mem_degree_two :
    MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) ∈
      MvPolynomial.homogeneousSubmodule (Fin 2) ℚ 2 := by
  have h := SetLike.mul_mem_graded X0_mem_degree_one X1_mem_degree_one
  simpa using h

/-- The open overlap of the two charts: D_+(X0 X1) = D_+(X0) cap D_+(X1). -/
noncomputable def overlapOpen : (projectiveLine).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)
    (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))

/-- The overlap is the intersection of the two chart opens. -/
theorem overlapOpen_eq_inf :
    overlapOpen = Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)
        (MvPolynomial.X (0 : Fin 2)) ⊓
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)
        (MvPolynomial.X (1 : Fin 2)) :=
  Proj.basicOpen_mul ..

/-- The chart images are exactly the principal open subschemes D_+(X0), D_+(X1). -/
theorem chart0_opensRange :
    chart0.opensRange = Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)
      (MvPolynomial.X (0 : Fin 2)) :=
  Proj.opensRange_awayι ..

theorem chart1_opensRange :
    chart1.opensRange = Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)
      (MvPolynomial.X (1 : Fin 2)) :=
  Proj.opensRange_awayι ..

/-- The actual overlap of the two charts: its coordinate ring is the homogeneous
localization at X0 X1 (this is where the transition t = lambda^{-1} lives). -/
noncomputable def overlapIso :
    (overlapOpen).toScheme ≅
      Spec (CommRingCat.of
        (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)
          (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)))) :=
  Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)
    (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))
    X0_mul_X1_mem_degree_two (by norm_num)

#print axioms chart0_opensRange
#print axioms chart1_opensRange
#print axioms overlapIso

end LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineChartsActual