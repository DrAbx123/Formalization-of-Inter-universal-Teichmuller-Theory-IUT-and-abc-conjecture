import tmp.sheaf.xif.paper.S1422HDDDetActual
import Mathlib.Tactic

/-!
# A1061: candidate det-root unit from qroot powers

Status: CANDIDATE + EXACT FAILURE COMMENT. No manual compile.

The existing actual detData unit is S1422.dependentPrimeUnit:
  (v : {v // v in s}) -> (S1402DependentE s v)ˣ
with coordinate (p_v)⁻¹ (prime-inverse diagonal), and S1422.detDataOfHull uses it
as the multiplicative dilation G of the dependent local-field product.

S3050Unit and S3016StepVQPilot are Real log-volumes, not group units.  The lana
source has the faithful tensor shape
  scaleEltAt ... = incl(qroot^{j^2})
(Iut/Concrete/ThetaRegion.lean:126-132), but that module is not built/importable
in this project (no olean here), and its tensor is not S1422's dependent product
unit.  Therefore the following candidate is a real, definitional finite-product
diagonal unit from supplied qroot powers, but it is NOT identified with
S1422.dependentPrimeUnit or with lana scaleEltAt.  The identification is the
exact GAP-DET-QROOT and is not asserted here.
-/

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1DetRootUnitActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1422HDDDetActual

/-- Coordinate root unit: a nonzero qroot raised to a natural exponent. -/
noncomputable def rootUnitAt
    (K : Type) [Field K] (qroot : K) (hq : qroot ≠ 0) (m : Nat) : Kˣ :=
  Units.mk0 (qroot ^ m) (pow_ne_zero m hq)

theorem rootUnitAt_apply
    (K : Type) [Field K] (qroot : K) (hq : qroot ≠ 0) (m : Nat) :
    (rootUnitAt K qroot hq m : K) = qroot ^ m := rfl

/-- Candidate dependent det unit: the diagonal product of supplied qroot powers.
This is the product-field unit with coordinate qroot v ^ m v; it is a genuine
finite product (not an arbitrary region map). -/
noncomputable def detRootUnit
    (s : Finset (NumberField.FinitePlace ℚ))
    (qroot : (v : {v // v ∈ s}) → S1402DependentE s v)
    (hq : ∀ v, qroot v ≠ 0)
    (m : {v // v ∈ s} → Nat) : (dependentPoint s)ˣ :=
  MulEquiv.piUnits.symm (fun v => rootUnitAt (S1402DependentE s v) (qroot v) (hq v) (m v))

/-- The diagonal identity, by definition unfolding: the underlying point of the
candidate det unit is the finite family qroot v ^ m v. -/
theorem detRootUnit_coe
    (s : Finset (NumberField.FinitePlace ℚ))
    (qroot : (v : {v // v ∈ s}) → S1402DependentE s v)
    (hq : ∀ v, qroot v ≠ 0)
    (m : {v // v ∈ s} → Nat) :
    ((detRootUnit s qroot hq m : dependentPoint s)ˣ : dependentPoint s) =
      fun v => qroot v ^ m v := by
  funext v
  simp [detRootUnit, rootUnitAt]

/-- Exact failure comment, checked as a theorem statement only: the candidate is
NOT S1422.dependentPrimeUnit.  There is no generic equality; only the special
choice qroot v = (dependentPlacePrime s v)⁻¹, m = 1 would recover the existing
prime-inverse unit, and even that requires a proof of the coordinate identity.
This declaration is intentionally absent; the proposition below records the
shape of the missing bridge without asserting it. -/
def DetRootUnitMatchesDependentPrimeUnit
    (s : Finset (NumberField.FinitePlace ℚ)) : Prop :=
  ∃ (qroot : (v : {v // v ∈ s}) → S1402DependentE s v)
    (hq : ∀ v, qroot v ≠ 0) (m : {v // v ∈ s} → Nat),
    detRootUnit s qroot hq m = dependentPrimeUnit s

/-- The existing detData uses dependentPrimeUnit, not detRootUnit.  This is
definitional and records the exact mismatch; it does not identify the two. -/
theorem dependentDetDataOfChar_uses_primeUnit
    (s : Finset (NumberField.FinitePlace ℚ))
    (hchar : DependentProductScalingChar s) :
    (dependentDetDataOfChar s hchar).detTensorPower =
      fun S => dependentPrimeUnit s • S := rfl

#check rootUnitAt
#check detRootUnit
#check detRootUnit_coe
#check DetRootUnitMatchesDependentPrimeUnit
#check dependentDetDataOfChar_uses_primeUnit

end LeanFormal.IUT.XiFPaper.Mzk1DetRootUnitActual
