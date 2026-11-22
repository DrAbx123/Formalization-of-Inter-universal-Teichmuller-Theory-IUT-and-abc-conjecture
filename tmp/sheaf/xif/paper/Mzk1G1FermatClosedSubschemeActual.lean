/- G1a Fermat closed subscheme of P2 via vanishing ideal. -/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open MvPolynomial ProjectiveSpectrum
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatClosedSubschemeActual
attribute [local instance] MvPolynomial.gradedAlgebra
abbrev A : Type := MvPolynomial (Fin 3) ℚ
abbrev 𝒜 : ℕ → Submodule ℚ A := MvPolynomial.homogeneousSubmodule (Fin 3) ℚ
abbrev P2 : Scheme := ProjectiveSpectrum.Proj (𝒜 := 𝒜)
def fermatPolynomial (n : ℕ) : A := X 0 ^ n + X 1 ^ n - X 2 ^ n
noncomputable def fermatClosed (n : ℕ) : TopologicalSpace.Closeds P2 :=
  ⟨ProjectiveSpectrum.zeroLocus 𝒜 {fermatPolynomial n},
    ProjectiveSpectrum.isClosed_zeroLocus 𝒜 {fermatPolynomial n}⟩
noncomputable def fermatIdealSheaf (n : ℕ) : P2.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (fermatClosed n)
noncomputable def FermatCurve (n : ℕ) : Scheme := (fermatIdealSheaf n).subscheme
noncomputable def fermatCurveι (n : ℕ) : FermatCurve n ⟶ P2 :=
  (fermatIdealSheaf n).subschemeι
#print axioms fermatCurveι
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatClosedSubschemeActual
