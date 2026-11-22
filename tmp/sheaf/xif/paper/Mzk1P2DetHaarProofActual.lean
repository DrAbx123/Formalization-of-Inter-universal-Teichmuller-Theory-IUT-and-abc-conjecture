import tmp.sheaf.xif.paper.Mzk1CanonicalHaarCoordLatticeActual
import tmp.sheaf.xif.paper.Mzk1GLActContinuousActionActual
import tmp.sheaf.xif.paper.Mzk1CanonicalDiagUncondFinalActual
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic

/-! # P2 determinant-Haar proof step

Fixed Haar: mu = addHaarMeasure coordinateCompacts, with mu(coordLattice)=1.

Actual results:
* the Haar scalar factor of any continuous linear equivalence equals the
  mu-mass of the image of coordLattice;
* lattice-preserving equivalences have scalar 1 (GL_d(Z_p) case);
* the diagonal p^e volume ratio is B4's unconditional ratio.

The only remaining step is the SNF decomposition of an arbitrary element of
GL_d(Q_p) into U diag(p^e) W with U,W lattice-preserving; this is recorded
as the exact missing datum.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory MeasureTheory.Measure
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P2DetHaarProofActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1MatrixHaarBaseActual
open LeanFormal.IUT.XiFPaper.Mzk1CanonicalHaarCoordLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1CanonicalHaarInvarianceActual
open LeanFormal.IUT.XiFPaper.Mzk1GLActContinuousActionActual
open LeanFormal.IUT.XiFPaper.Mzk1CanonicalDiagUncondFinalActual
open LeanFormal.IUT.PadicIntegerProductLattice

variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]
variable [MeasurableSpace (d -> ℚ_[p])] [BorelSpace (d -> ℚ_[p])]

/-- The fixed canonical additive Haar used in B4. -/
noncomputable abbrev p2Haar : Measure (d -> ℚ_[p]) :=
  addHaarMeasure (coordinateCompacts (p := p) (d := d))

/-- Openness of the coordinate lattice in the canonical topology. -/
theorem p2_coordLattice_open :
    IsOpen (coordLattice (p := p) (d := d) : Set (d -> ℚ_[p])) := by
  rw [coordLattice_eq_padicIntegerCoordinateLattice]
  exact isOpen_padicIntegerCoordinateLattice

/-- Mass of the coordinate lattice for the fixed Haar is 1. -/
theorem p2_coordLattice_mass :
    p2Haar (coordLattice (p := p) (d := d)) = 1 :=
  coordinateCompacts_mass

/-- Pushforward of the fixed Haar by a continuous linear equivalence is Haar. -/
theorem p2_map_haar (L : (d -> ℚ_[p]) ≃L[ℚ_[p]] (d -> ℚ_[p])) :
    IsAddHaarMeasure ((p2Haar).map L) :=
  ContinuousLinearEquiv.isAddHaarMeasure_map L (p2Haar)

/-- Haar uniqueness evaluated on the open coordinate lattice. -/
theorem p2_map_coordLattice_eq_scalar_smul
    (L : (d -> ℚ_[p]) ≃L[ℚ_[p]] (d -> ℚ_[p])) :
    ((p2Haar).map L)
        (coordLattice (p := p) (d := d)) =
      addHaarScalarFactor ((p2Haar).map L)
          (p2Haar) •
        (p2Haar) (coordLattice (p := p) (d := d)) := by
  haveI : IsAddHaarMeasure ((p2Haar).map L) :=
    p2_map_haar L
  exact measure_isAddHaarMeasure_eq_smul_of_isOpen
    ((p2Haar).map L) (p2Haar)
    (p2_coordLattice_open (p := p) (d := d))

/-- Scalar factor = mass of the lattice image, because the lattice has mass 1. -/
theorem p2_scalar_eq_lattice_image
    (L : (d -> ℚ_[p]) ≃L[ℚ_[p]] (d -> ℚ_[p])) :
    addHaarScalarFactor ((p2Haar).map L)
        (p2Haar) =
      ((p2Haar).map L) (coordLattice (p := p) (d := d)) := by
  have h := p2_map_coordLattice_eq_scalar_smul (p := p) (d := d) L
  rw [p2_coordLattice_mass] at h
  simpa using h.symm

/-- Lattice-preserving equivalence has Haar scalar 1. -/
theorem p2_lattice_preserving_scalar_one
    (L : (d -> ℚ_[p]) ≃L[ℚ_[p]] (d -> ℚ_[p]))
    (h : L '' coordLattice (p := p) (d := d) =
      coordLattice (p := p) (d := d)) :
    (p2Haar).map L = p2Haar :=
  canonical_map_eq_of_image_eq_full L h

/-- Exact remaining step: SNF decomposition of an arbitrary GL_d(Q_p) element. -/
def detHaarSNFMissing : List String :=
  [ "SNF decomposition L = U * diag(p^e) * W with U,W lattice-preserving for arbitrary L in GL_d(Q_p)",
    "composition of the three Haar scalars (GL=1, diagonal=B4, scalar p^m by FinitePadicHaarScaling)" ]

theorem detHaarSNFMissing_length : detHaarSNFMissing.length = 2 := rfl

#check p2_coordLattice_mass
#check p2_map_coordLattice_eq_scalar_smul
#check p2_scalar_eq_lattice_image
#check p2_lattice_preserving_scalar_one
#check detHaarSNFMissing
end LeanFormal.IUT.XiFPaper.Mzk1P2DetHaarProofActual
end
