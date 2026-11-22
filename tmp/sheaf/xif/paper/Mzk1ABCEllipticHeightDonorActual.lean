/- ABC elliptic-height donor: actual data assembled from the rational Frey curve of
an ABC triple (discriminant, its radical, j-invariant denominator) and the
actual criterion-to-ABC implication.  All ingredients are existing actual
donors; no new axiom. -/
import LeanFormal.IUT.ABCBridge.Bridge.ABCEllipticHeightCriterion
import LeanFormal.IUT.ABCBridge.Geometry.FreyDiscriminantRadical
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantLocalHeight
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantRadicalBridge
import LeanFormal.IUT.ABCBridge.Bridge.FreyOddConductorHeightCriterion
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ABCEllipticHeightDonorActual

open LeanFormal.IUT

/-- Actual elliptic-height data of an ABC triple, built from the rational Frey
curve: the natural-number discriminant, its radical, the recovered product
radical, and the j-invariant denominator. -/
structure ABCEllipticHeightData (a b c : Nat) where
  htriple : IsABCTriple a b c
  freyDiscriminant : Nat
  discriminant_eq : freyDiscriminant = 16 * a ^ 2 * b ^ 2 * c ^ 2
  freyDiscriminantRadical : Nat
  freyDiscriminantRadical_eq : freyDiscriminantRadical = natRadical freyDiscriminant
  freyDiscriminantRadical_eq_product :
    freyDiscriminantRadical = natRadical (a * b * c)
  jDen : Nat
  jDen_eq : jDen = (abcJInvariant a b c).den

/-- The actual elliptic-height data of any ABC triple. -/
def abcEllipticHeightData {a b c : Nat} (h : IsABCTriple a b c) :
    ABCEllipticHeightData a b c where
  htriple := h
  freyDiscriminant := 16 * a ^ 2 * b ^ 2 * c ^ 2
  discriminant_eq := rfl
  freyDiscriminantRadical := natRadical (16 * a ^ 2 * b ^ 2 * c ^ 2)
  freyDiscriminantRadical_eq := rfl
  freyDiscriminantRadical_eq_product :=
    h.natRadical_freyDiscriminant_eq_natRadical_product
  jDen := (abcJInvariant a b c).den
  jDen_eq := rfl

/-- The actual Frey discriminant of the data is the cast of the natural-number
discriminant. -/
theorem abcEllipticHeightData_discriminant {a b c : Nat}
    (D : ABCEllipticHeightData a b c) :
    (rationalFreyWeierstrassCurve a b).Δ = (D.freyDiscriminant : Rat) := by
  rw [D.discriminant_eq]
  exact rationalFreyWeierstrassCurve_discriminant_natCast_sixteen_mul_sq_of_isABCTriple
    D.htriple

/-- The actual Frey discriminant radical equals the product radical. -/
theorem abcEllipticHeightData_radical {a b c : Nat}
    (D : ABCEllipticHeightData a b c) :
    D.freyDiscriminantRadical = natRadical (a * b * c) :=
  D.freyDiscriminantRadical_eq_product

/-- Actual criterion-to-ABC implication: the uniform Frey j-height criterion
implies the ABC statement (= ABCConjecture) via the existing equivalence. -/
theorem abcStatement_of_freyJProductHeightCriterion
    (h : ABCFreyJProductHeightCriterion) : ABCConjecture :=
  (abcConjecture_iff_freyJProductHeightCriterion).mpr h

/-- The same implication with the actual elliptic-height data package. -/
theorem abcStatement_of_heightData {a b c : Nat}
    (D : ABCEllipticHeightData a b c)
    (h : ABCFreyJProductHeightCriterion) : ABCConjecture :=
  abcStatement_of_freyJProductHeightCriterion h

#print axioms abcEllipticHeightData
#print axioms abcEllipticHeightData_discriminant
#print axioms abcEllipticHeightData_radical
#print axioms abcStatement_of_freyJProductHeightCriterion
#print axioms abcStatement_of_heightData

end LeanFormal.IUT.XiFPaper.Mzk1ABCEllipticHeightDonorActual
end
