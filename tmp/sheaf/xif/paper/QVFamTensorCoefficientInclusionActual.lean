import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice

/-! # Theta tensor scaled region inside the q-pilot tensor region

For each bad place b and each nonzero theta label j, the qVFamily order
coefficient is c b >= 0 and the theta coefficient is j^2 * c b with j^2 >= 1.
The fractional lattice is antitone in the exponent, so

  F (j^2 * c) <= F c,

and multiplying by the fixed holomorphic lattice preserves the inclusion:

  F (j^2*c) * O_hol <= F c * O_hol.

This is exactly the actual thetaTensorScaledRegion j subset qPilotRegion.
No gap/fake assumption; the only hypothesis is the actual j^2 >= 1 (nonzero
label).  No inequality between log-volumes is asserted.  No sorry/axiom. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientInclusionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual q-pilot tensor region at coefficient c b. -/
noncomputable def qVFamQPilotRegion : Set (qVFamTensorBlock T b) :=
  thetaTensorScaledRegion
    (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
    (fun _ : qVFamTensorV => qVFamTensorCoefficient T b)

/-- Actual coefficient inequality: c b <= j^2 * c b for j^2 >= 1 and c b >= 0. -/
theorem qVFamTensorCoefficient_le_thetaCoefficient
    (j : SignedLabel l.value)
    (hj : 1 ≤ (gaussExponent j.1).toNat) :
    ∀ i : qVFamTensorV,
      (fun _ : qVFamTensorV => qVFamTensorCoefficient T b) i ≤
        qVFamThetaTensorCoefficient T b j i := by
  intro i
  unfold qVFamThetaTensorCoefficient
  have hc : 0 ≤ qVFamTensorCoefficient T b :=
    qVFamTensorCoefficient_nonneg T b
  have hjreal : (1 : Real) ≤ ((gaussExponent j.1).toNat : Real) := by
    exact_mod_cast hj
  nlinarith [mul_nonneg (sub_nonneg.mpr hjreal) hc]

/-- The actual theta tensor region is contained in the q-pilot tensor region. -/
theorem qVFamThetaTensorRegion_subset_qPilotRegion
    (j : SignedLabel l.value)
    (hj : 1 ≤ (gaussExponent j.1).toNat) :
    qVFamThetaTensorRegion T b j ⊆ qVFamQPilotRegion T b := by
  unfold qVFamThetaTensorRegion qVFamQPilotRegion thetaTensorScaledRegion
  have hF : arithmeticTupleFractionalLattice
      (qVFamTensorPlaces T b) qVFamTensorTuple
        (qVFamThetaTensorCoefficient T b j) ≤
      arithmeticTupleFractionalLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple
        (fun _ : qVFamTensorV => qVFamTensorCoefficient T b) :=
    arithmeticTupleFractionalLattice_mono
      (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
      (a := fun _ : qVFamTensorV => qVFamTensorCoefficient T b)
      (b := qVFamThetaTensorCoefficient T b j)
      (qVFamTensorCoefficient_le_thetaCoefficient T b j hj)
  have hmul : arithmeticTupleFractionalLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple
          (qVFamThetaTensorCoefficient T b j) *
        arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b)
          qVFamTensorTuple ≤
      arithmeticTupleFractionalLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple
          (fun _ : qVFamTensorV => qVFamTensorCoefficient T b) *
        arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b)
          qVFamTensorTuple := by
    apply Submodule.mul_le.mpr
    intro x hx y hy
    exact Submodule.mul_mem_mul (hF hx) hy
  intro z hz
  exact hmul hz

end LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientInclusionActual

end
