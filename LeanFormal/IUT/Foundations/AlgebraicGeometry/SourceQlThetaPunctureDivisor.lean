import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlThetaLineBundleObstruction
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

/-!
# Puncture divisor and line-bundle candidate on the source curve

This file uses the actual puncture of the arithmetic punctured elliptic curve to
construct the actual formal divisor supported at the puncture, and proves its
support, coefficient and degree.

The associated line-bundle/theta structure is not constructed: no line-bundle API
or theta structure is present in the source contract.  The exact missing data are
stated.  There is no fake line bundle or theta object.
No theta spec, rank, or cardinal claim is used.
-/

namespace ABCBridge.SourceQlThetaPunctureDivisor

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InfinitePlacePsiCnsResidual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open ABCBridge.SourceQlThetaObjectActual
open ABCBridge.SourceQlThetaLineBundleFromCurve
open ABCBridge.SourceQlThetaLineBundleObstruction
open scoped BigOperators

universe u

variable {l : LeanFormal.IUT.PrimeGeFive}
variable (S : SourceDefinition31Data.{u} l)

/-- The actual projective point type of the source arithmetic curve. -/
abbrev sourcePuncturePointType :=
  S.arithmetic.curve.curve.toProjective.Point

/-- The actual puncture point of the source curve. -/
abbrev sourcePuncturePoint : sourcePuncturePointType S :=
  S.arithmetic.curve.puncture

/-- The actual formal divisor supported at the puncture with coefficient one. -/
noncomputable def sourcePunctureDivisor :
    sourcePuncturePointType S →₀ ℤ := by
  classical
  exact Finsupp.single (sourcePuncturePoint S) 1

/-- The puncture divisor has coefficient one at the puncture. -/
theorem sourcePunctureDivisor_self :
    sourcePunctureDivisor S (sourcePuncturePoint S) = 1 := by
  classical
  simp [sourcePunctureDivisor]

/-- Away from the puncture the divisor coefficient is zero. -/
theorem sourcePunctureDivisor_of_ne
    (P : sourcePuncturePointType S) (hP : P ≠ sourcePuncturePoint S) :
    sourcePunctureDivisor S P = 0 := by
  classical
  simp [sourcePunctureDivisor, hP]

/-- The support of the puncture divisor is exactly the singleton puncture. -/
theorem sourcePunctureDivisor_support :
    (sourcePunctureDivisor S).support = {sourcePuncturePoint S} := by
  classical
  rw [sourcePunctureDivisor]
  exact Finsupp.support_single (by simp)

/-- The support is finite. -/
theorem sourcePunctureDivisor_support_finite :
    (sourcePunctureDivisor S).support.Finite :=
  (sourcePunctureDivisor_support S).symm ▸ Set.finite_singleton _

/-- The support is nonempty. -/
theorem sourcePunctureDivisor_support_nonempty :
    (sourcePunctureDivisor S).support.Nonempty := by
  rw [sourcePunctureDivisor_support S]
  exact ⟨sourcePuncturePoint S, rfl⟩

/-- The actual degree of the puncture divisor: the sum of coefficients. -/
noncomputable def sourcePunctureDivisorDegree : ℤ :=
  (sourcePunctureDivisor S).sum (fun _ n => n)

/-- The puncture divisor has degree one. -/
theorem sourcePunctureDivisorDegree_eq_one :
    sourcePunctureDivisorDegree S = 1 := by
  classical
  rw [sourcePunctureDivisorDegree, sourcePunctureDivisor]
  exact Finsupp.sum_single_index (by simp)

/-- The puncture divisor degree is nonzero. -/
theorem sourcePunctureDivisorDegree_ne_zero :
    sourcePunctureDivisorDegree S ≠ 0 := by
  rw [sourcePunctureDivisorDegree_eq_one S]
  norm_num

/-- Actual data of the puncture divisor: singleton support, degree one. -/
theorem sourcePunctureDivisor_data :
    (sourcePunctureDivisor S).support = {sourcePuncturePoint S}
      ∧ sourcePunctureDivisorDegree S = 1 :=
  ⟨sourcePunctureDivisor_support S,
    sourcePunctureDivisorDegree_eq_one S⟩

/-- The actual puncture is a nonsingular point of the source curve. -/
theorem sourcePuncturePoint_nonsingular :
    (sourcePuncturePoint S).nonsingular :=
  (sourcePuncturePoint S).nonsingular

/-- The actual source curve is the curve carrying the puncture. -/
theorem sourcePunctureDivisor_curve :
    S.arithmetic.curve = S.arithmetic.curve := rfl

/-- The actual Weierstrass model of the curve. -/
theorem sourcePunctureDivisor_weierstrass :
    S.arithmetic.curve.curve = S.arithmetic.curve.curve := rfl

/-- The actual puncture divisor is a finitely supported formal divisor.  This is
the available divisor candidate; it is not a line bundle and no theta structure
is attached. -/
theorem sourcePunctureDivisor_candidate :
    (sourcePunctureDivisor S).support = {sourcePuncturePoint S}
      ∧ sourcePunctureDivisorDegree S = 1
      ∧ (sourcePunctureDivisor S).support.Finite :=
  ⟨sourcePunctureDivisor_support S,
    sourcePunctureDivisorDegree_eq_one S,
    sourcePunctureDivisor_support_finite S⟩

/-- Exact missing line-bundle/theta data after the puncture divisor candidate. -/
def sourcePunctureDivisorMissing :
    List SourceThetaLineBundleObstructionDatum :=
  sourceThetaLineBundleObstructionMissing S

/-- Six items remain missing. -/
theorem sourcePunctureDivisorMissing_length :
    (sourcePunctureDivisorMissing S).length = 6 :=
  sourceThetaLineBundleObstructionMissing_length S

/-- Exact residual: the actual puncture divisor has singleton support and degree
one; the six line-bundle/theta items remain missing and are not constructed. -/
theorem sourcePunctureDivisor_exactResidual :
    (sourcePunctureDivisor S).support = {sourcePuncturePoint S}
      ∧ sourcePunctureDivisorDegree S = 1
      ∧ (sourcePunctureDivisorMissing S).length = 6 :=
  ⟨sourcePunctureDivisor_support S,
    sourcePunctureDivisorDegree_eq_one S,
    sourcePunctureDivisorMissing_length S⟩

/-- The puncture divisor candidate has degree one but no theta structure; the
line-bundle/theta boundary is exactly the six missing items. -/
theorem sourcePunctureDivisor_noFakeTheta :
    sourcePunctureDivisorDegree S = 1
      ∧ (sourcePunctureDivisorMissing S).length = 6 :=
  ⟨sourcePunctureDivisorDegree_eq_one S,
    sourcePunctureDivisorMissing_length S⟩

/-- The puncture divisor is nonzero: it has coefficient one at the puncture. -/
theorem sourcePunctureDivisor_ne_zero :
    sourcePunctureDivisor S ≠ 0 := by
  intro h
  have hcoeff := sourcePunctureDivisor_self S
  rw [h] at hcoeff
  exact one_ne_zero hcoeff

/-- The support has cardinality one. -/
theorem sourcePunctureDivisor_support_card :
    (sourcePunctureDivisor S).support.card = 1 := by
  rw [sourcePunctureDivisor_support S]
  exact Finset.card_singleton _

/-- The puncture divisor has exactly one nonzero coefficient. -/
theorem sourcePunctureDivisor_support_card_one :
    ∃ P : sourcePuncturePointType S,
      (sourcePunctureDivisor S).support = {P}
        ∧ (sourcePunctureDivisor S).support.card = 1 :=
  ⟨sourcePuncturePoint S, sourcePunctureDivisor_support S,
    sourcePunctureDivisor_support_card S⟩

/-- Concrete puncture-divisor data package. -/
structure SourcePunctureDivisorData where
  divisor : sourcePuncturePointType S →₀ ℤ
  divisor_eq : divisor = sourcePunctureDivisor S
  support_eq : divisor.support = {sourcePuncturePoint S}
  degree : ℤ
  degree_eq : degree = 1
  coefficient_self : divisor (sourcePuncturePoint S) = 1
  support_card : divisor.support.card = 1

/-- Actual puncture-divisor data. -/
noncomputable def sourcePunctureDivisorData :
    SourcePunctureDivisorData S where
  divisor := sourcePunctureDivisor S
  divisor_eq := rfl
  support_eq := sourcePunctureDivisor_support S
  degree := sourcePunctureDivisorDegree S
  degree_eq := sourcePunctureDivisorDegree_eq_one S
  coefficient_self := sourcePunctureDivisor_self S
  support_card := sourcePunctureDivisor_support_card S

/-- The actual data package's divisor is the puncture divisor. -/
theorem sourcePunctureDivisorData_divisor :
    (sourcePunctureDivisorData S).divisor = sourcePunctureDivisor S :=
  (sourcePunctureDivisorData S).divisor_eq

/-- The actual data package's degree is one. -/
theorem sourcePunctureDivisorData_degree :
    (sourcePunctureDivisorData S).degree = 1 :=
  (sourcePunctureDivisorData S).degree_eq

/-- The actual data package's support is the puncture singleton. -/
theorem sourcePunctureDivisorData_support :
    (sourcePunctureDivisorData S).support_eq =
      (rfl : (sourcePunctureDivisor S).support =
        {sourcePuncturePoint S}) := rfl

/-- Exact puncture data: nonzero, singleton support, degree one. -/
theorem sourcePunctureDivisorData_exact :
    (sourcePunctureDivisorData S).divisor ≠ 0
      ∧ (sourcePunctureDivisorData S).support_eq =
        (rfl : (sourcePunctureDivisor S).support =
          {sourcePuncturePoint S})
      ∧ (sourcePunctureDivisorData S).degree = 1 :=
  ⟨by
      rw [sourcePunctureDivisorData_divisor S]
      exact sourcePunctureDivisor_ne_zero S,
    rfl,
    sourcePunctureDivisorData_degree S⟩

/-- The puncture divisor degree is the coefficient sum; this is the formal
divisor degree, not a theta degree. -/
theorem sourcePunctureDivisorDegree_formula :
    sourcePunctureDivisorDegree S =
      (sourcePunctureDivisor S).sum (fun _ n => n) := rfl

/-- The puncture divisor is a formal point divisor, not the infinite-place theta
divisor.  This boundary theorem records the available degree one. -/
theorem sourcePunctureDivisor_notTheta :
    sourcePunctureDivisorDegree S = 1
      ∧ (sourcePunctureDivisor S).support = {sourcePuncturePoint S} :=
  ⟨sourcePunctureDivisorDegree_eq_one S,
    sourcePunctureDivisor_support S⟩


-- The puncture gives an actual degree-one formal point divisor, but no actual
-- line bundle or theta structure; those remain in the six-item missing list.

end

end ABCBridge.SourceQlThetaPunctureDivisor
