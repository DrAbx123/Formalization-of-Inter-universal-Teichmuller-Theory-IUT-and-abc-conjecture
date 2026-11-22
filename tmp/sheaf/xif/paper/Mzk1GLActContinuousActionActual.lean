/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1GLActContinuousActual
import tmp.sheaf.xif.paper.Mzk1CanonicalHaarCoordLatticeActual

/-! # Action of the packaged GL automorphism (task-109) -/
noncomputable section
open scoped BigOperators
open MeasureTheory
open MeasureTheory.Measure
namespace LeanFormal.IUT.XiFPaper.Mzk1GLActContinuousActionActual
open LeanFormal.IUT.XiFPaper.Mzk1GLActContinuousActual
open LeanFormal.IUT.XiFPaper.Mzk1MatrixHaarBaseActual
variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]
variable [MeasurableSpace (d → ℚ_[p])] [BorelSpace (d → ℚ_[p])]
theorem glContinuousLinearEquiv_apply
    (V : Matrix.GeneralLinearGroup d (PadicInt p)) (x : d → ℚ_[p]) :
    glContinuousLinearEquiv V x = glAct p d V.1 x := by
  rfl

theorem glContinuous_image_coordLattice
    (V : Matrix.GeneralLinearGroup d (PadicInt p)) :
    glContinuousLinearEquiv (p := p) V '' coordLattice (p := p) (d := d) =
      coordLattice (p := p) (d := d) := by
  have hVW : V.1 * (V⁻¹).1 = (1 : Matrix d d (PadicInt p)) := by
    have := congrArg Units.val (mul_inv_cancel V)
    simpa using this
  rw [show (glContinuousLinearEquiv (p := p) V : (d → ℚ_[p]) → (d → ℚ_[p])) =
      glAct (p := p) d V.1 from funext fun x => glContinuousLinearEquiv_apply V x]
  exact glAct_image_eq_of_mul_eq_one (p := p) (d := d) V.1 (V⁻¹).1 hVW

theorem glContinuous_canonical_haar_invariant
    (V : Matrix.GeneralLinearGroup d (PadicInt p)) :
    (addHaarMeasure (LeanFormal.IUT.XiFPaper.Mzk1CanonicalHaarCoordLatticeActual.coordinateCompacts (p := p) (d := d))).map
        (glContinuousLinearEquiv (p := p) V) =
      addHaarMeasure (LeanFormal.IUT.XiFPaper.Mzk1CanonicalHaarCoordLatticeActual.coordinateCompacts (p := p) (d := d)) :=
  LeanFormal.IUT.XiFPaper.Mzk1CanonicalHaarCoordLatticeActual.canonical_map_eq_of_image_eq_full
    (glContinuousLinearEquiv (p := p) V) (glContinuous_image_coordLattice V)
def glActActionRows : List (String × String) :=
  [ ("glContinuousLinearEquiv_apply", "green rfl"),
    ("lattice image under GL", "GAP"),
    ("canonical full B4 application", "GAP") ]
theorem glActActionRows_length : glActActionRows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1GLActContinuousActionActual
