import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlThetaLineBundleFromCurve
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlThetaLineBundleObstruction
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceThetaDivisor

/-!
# Source theta function/line bundle: actual divisor object and exact missing fields

Source anchors:

* IUT II, Introduction, p.2 (extraction lines 69-109): the theta function
  Theta_v = (sqrt(-1) * sum_m q_v^((m+1/2)^2/2))^(-1) *
  sum_n (-1)^n q_v^((n+1/2)^2/2) U_v^(n+1/2), evaluated at l-torsion points;
  the resulting theta values are q_v^(j^2) up to a 2l-th root of unity.
* IUT II, Remark 2.5.1, p.72-73 (lines 4356-4396): for j in Fl, the set
  theta_j(Π_v) is precisely the mu_(2l)-orbit of the theta value q_v^(j^2).
* IUT III, Definition 3.8, (i), p.112 (lines 6731-6769): the Theta-pilot object
  is the arithmetic divisor determined by the zero locus of the theta values
  {q_j^2}; the q-pilot object is determined by the q_v.
* IUT III, Corollary 3.12, p.174 (lines 10499-10529).

Actually available in the tree and constructed below:
* the source arithmetic curve and Weierstrass model;
* the source theta-divisor type SourceThetaDivisor S (integer coefficients on
  infinite places), its weighted degree, and the actual zero divisor with
  degree zero and Galois invariance;
* the actual full real principal divisor of a global unit and its product
  formula (finite integer part plus real archimedean part).

Not available in the tree: the theta line bundle on the source curve, the theta
object A_Theta, the theta function/global section, the identification of its
zero divisor with the {q_j^2} divisor, the q-pilot arithmetic divisor, and the
Theta-link identification. These are recorded as an exact missing structure,
never replaced by the value-layer hull or by a fake line bundle.

No inequality is asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace ABCBridge.SourceThetaFunctionLineBundleActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaGenerator
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaDivisor
open ABCBridge.SourceQlThetaLineBundleFromCurve
open ABCBridge.SourceQlThetaLineBundleObstruction
open LeanFormal.IUT.InfinitePlacePsiCnsResidual

universe u

variable {l : PrimeGeFive}
variable (S : SourceDefinition31Data.{u} l)

/-- The actual source arithmetic curve. -/
abbrev actualThetaCurve : PuncturedEllipticCurve S.arithmetic.F :=
  sourceThetaLineBundleCurve S

/-- The actual source theta-divisor type. -/
abbrev actualThetaDivisorType : Type u :=
  sourceThetaLineBundleDivisorType S

/-- The actual theta-divisor zero object. -/
def actualThetaZeroDivisor : actualThetaDivisorType S :=
  sourceThetaLineBundleZeroDivisor S

/-- The actual weighted degree of the theta-divisor type. -/
def actualThetaDivisorDegree (D : actualThetaDivisorType S) : ℤ :=
  sourceThetaLineBundleDegree S D

/-- Actual zero divisor degree is zero. -/
theorem actualThetaZeroDivisor_degree :
    actualThetaDivisorDegree S (actualThetaZeroDivisor S) = 0 :=
  sourceThetaLineBundleZeroDivisor_degree S

/-- Actual zero divisor is Galois invariant. -/
theorem actualThetaZeroDivisor_galois :
    sourceThetaLineBundleGalois S (actualThetaZeroDivisor S) :=
  sourceThetaLineBundleZeroDivisor_galois S

/-- The actual full real divisor type (finite part plus archimedean part). -/
abbrev actualThetaFullRealDivisorType : Type u :=
  sourceThetaFullRealDivisorType S

/-- Actual full real principal divisor of a global unit. -/
def actualThetaPrincipalDivisor (f : S.arithmetic.Fˣ) :
    actualThetaFullRealDivisorType S :=
  sourceThetaPrincipalDivisor S f

/-- The actual full real principal divisor has degree zero, by the product formula. -/
theorem actualThetaPrincipalDivisor_degree_zero (f : S.arithmetic.Fˣ) :
    sourceThetaFullRealDivisorDegree S
      (actualThetaPrincipalDivisor S f) = 0 :=
  sourceThetaPrincipalDivisor_degree_zero S f

/-- Actual theta-value family q_v^(j^2), indexed by the signed labels. This
is the actual q_v^(j^2) data of IUT II p.2-3 and Remark 2.5.1, p.72-73; it is
not the source theta divisor. -/
structure ActualQThetaValueData (t : AnalyticThetaCarrier) where
  value : SignedLabel l.value → ℝˣ
  value_eq : ∀ j, value j = thetaUnit t j.1
  qUnit : ℝˣ
  qUnit_eq : qUnit = thetaQUnit t
  pow_eq : ∀ j, value j = qUnit ^ (gaussExponent j.1).toNat
  value_ne_zero : ∀ j, (value j : ℝ) ≠ 0

/-- Actual q_v^(j^2) family from thetaUnit. -/
noncomputable def actualQThetaValueData (t : AnalyticThetaCarrier) :
    ActualQThetaValueData (l := l) t where
  value j := thetaUnit t j.1
  value_eq j := rfl
  qUnit := thetaQUnit t
  qUnit_eq := rfl
  pow_eq j := thetaUnit_eq_qUnit_pow t j.1
  value_ne_zero j := by
    have hpos : (0 : ℝ) < (thetaUnit t j.1 : ℝ) := by
      rw [thetaUnit_apply]
      exact realThetaValue_pos t.q_pos j.1
    exact ne_of_gt hpos

/-- Actual q_v^(j^2) family at the concrete Gaussian carrier q = 1/5. -/
noncomputable def actualQThetaValueDataConcrete :
    ActualQThetaValueData (l := l) analyticThetaCarrierConcrete :=
  actualQThetaValueData (l := l) analyticThetaCarrierConcrete

/-- The actual zero locus of the theta-value family in the real unit family. This
is empty because every thetaUnit is a nonzero unit. It is NOT the source theta
divisor of IUT II/III. -/
def actualQThetaValueZeroLocus (t : AnalyticThetaCarrier) :
    Set (SignedLabel l.value) :=
  {j | ((actualQThetaValueData (l := l) t).value j : ℝ) = 0}

/-- The actual theta-value zero locus is empty. -/
theorem actualQThetaValueZeroLocus_empty (t : AnalyticThetaCarrier) :
    actualQThetaValueZeroLocus (l := l) t = ∅ := by
  ext j
  simp only [actualQThetaValueZeroLocus, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false]
  exact (actualQThetaValueData (l := l) t).value_ne_zero j

/-- Exact missing source object: theta line bundle, theta object/function,
its global zero divisor, the q-pilot divisor, and the Theta-link
identification. The actual q_v^(j^2) family is supplied separately by
ActualQThetaValueData; the missing fields are not constructed values. -/
structure ThetaFunctionLineBundleMissing : Prop where
  curveLineBundle : Prop
  thetaObject : Prop
  thetaFunction : Prop
  thetaGlobalSection : Prop
  thetaZeroDivisorEq : Prop
  qPilotDivisor : Prop
  thetaLinkIdentification : Prop

/-- Exact missing field: the source theta function/line bundle package. -/
def MissingThetaFunctionLineBundle : Prop :=
  Nonempty (ThetaFunctionLineBundleMissing (S := S))

/-- The available object is divisor-level only; it does not contain a theta
line bundle, theta function, or the {q_j^2} global zero divisor. -/
theorem thetaFunctionLineBundle_available_is_divisor_only :
    actualThetaDivisorType S =
        (NumberField.InfinitePlace S.arithmetic.F → ℤ) ∧
      actualThetaDivisorDegree S (actualThetaZeroDivisor S) = 0 :=
  ⟨sourceThetaLineBundleDivisorType_eq S,
    sourceThetaLineBundleZeroDivisor_degree S⟩

end ABCBridge.SourceThetaFunctionLineBundleActual

end
