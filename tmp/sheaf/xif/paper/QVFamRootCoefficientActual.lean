import tmp.sheaf.xif.paper.QVPilotLatticeCoefficientPositiveActual

/-! # 2l-th-root qVFamily tensor coefficient

The qVFamily q_v gives the full coefficient c_b (order times residue-degree
weight).  The theta values use the 2l-th root q_v^{1/(2l)}, so the tensor
coefficient is

  c_root(b) = c_b / (2l)

as an actual real coefficient (fractional lattices allow real exponents).  The
root local log is

  rootLog b = - c_root(b) * log p_b = localQPilotLog b / (2l).

For the integer/valuation realization we also record the exact divisibility
condition (2l) | order(qVFamily b); under it a natural root order exponent is
constructed and its cast times 2l recovers the order.  No fake integrality is
asserted when the divisibility is absent; mu_{2l} ambiguity is not hidden.

No fake inequality/axiom/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVFamRootCoefficientActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.QVPilotLatticeCoefficientPositiveActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- The actual 2l denominator. -/
noncomputable def qVFamRootDenominator : Real :=
  (2 * l.value : Real)

/-- The denominator is nonzero. -/
theorem qVFamRootDenominator_ne_zero : qVFamRootDenominator (l := l) ≠ 0 := by
  unfold qVFamRootDenominator
  have h : (2 * l.value : Nat) ≠ 0 := Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  exact_mod_cast h

/-- The actual root tensor coefficient c_root = c / (2l). -/
noncomputable def qVFamRootCoefficient : Real :=
  qVFamilyLatticeCoefficient T b / qVFamRootDenominator (l := l)

/-- The root coefficient equals the full coefficient divided by 2l. -/
theorem qVFamRootCoefficient_eq :
    qVFamRootCoefficient T b =
      qVFamilyLatticeCoefficient T b / qVFamRootDenominator (l := l) := rfl

/-- Exact inverse relation: 2l * c_root = c. -/
theorem qVFamRootDenominator_mul_rootCoefficient :
    qVFamRootDenominator (l := l) * qVFamRootCoefficient T b =
      qVFamilyLatticeCoefficient T b := by
  unfold qVFamRootCoefficient
  field_simp [qVFamRootDenominator_ne_zero (l := l)]

/-- The root local q-pilot log: -(c_root * log p_b). -/
noncomputable def localQVRootLog : Real :=
  -qVFamRootCoefficient T b *
    Real.log (qVFamilyResiduePrime T b : Real)

/-- The root log is the full local q-pilot log divided by 2l. -/
theorem localQVRootLog_eq_half_localQPilotLog :
    qVFamRootDenominator (l := l) * localQVRootLog T b =
      localQPilotLog T b := by
  unfold localQVRootLog localQPilotLog
  rw [← qVFamRootDenominator_mul_rootCoefficient T b]
  ring

/-- Exact divisibility condition for an integral root order. -/
def QVFamOrderDivisibleByTwoL : Prop :=
  (2 * l.value) ∣ (qVFamily T b).order

/-- Natural root order exponent under the exact divisibility condition. -/
noncomputable def qVFamRootOrderExponent
    (h : QVFamOrderDivisibleByTwoL T b) : Nat :=
  (qVFamily T b).order / (2 * l.value)

/-- The natural root exponent recovers the full order under divisibility. -/
theorem qVFamRootOrderExponent_spec
    (h : QVFamOrderDivisibleByTwoL T b) :
    (qVFamRootOrderExponent T b h : Real) * qVFamRootDenominator (l := l) =
      ((qVFamily T b).order : Real) := by
  unfold qVFamRootOrderExponent qVFamRootDenominator
  have hnat := Nat.div_mul_cancel h
  exact_mod_cast hnat

/-- Actual root scalar data at b. -/
structure QVFamRootScalarData where
  denominator : Real
  denominator_eq : denominator = qVFamRootDenominator (l := l)
  rootCoefficient : Real
  rootCoefficient_eq : rootCoefficient = qVFamRootCoefficient T b
  rootLog : Real
  rootLog_eq : rootLog = localQVRootLog T b
  denominator_mul_rootCoefficient :
    denominator * rootCoefficient = qVFamilyLatticeCoefficient T b
  denominator_mul_rootLog : denominator * rootLog = localQPilotLog T b

/-- The actual root scalar data constructor. -/
noncomputable def qVFamRootScalarData : QVFamRootScalarData T b where
  denominator := qVFamRootDenominator (l := l)
  denominator_eq := rfl
  rootCoefficient := qVFamRootCoefficient T b
  rootCoefficient_eq := rfl
  rootLog := localQVRootLog T b
  rootLog_eq := rfl
  denominator_mul_rootCoefficient := qVFamRootDenominator_mul_rootCoefficient T b
  denominator_mul_rootLog := localQVRootLog_eq_half_localQPilotLog T b

end LeanFormal.IUT.XiFPaper.QVFamRootCoefficientActual

end