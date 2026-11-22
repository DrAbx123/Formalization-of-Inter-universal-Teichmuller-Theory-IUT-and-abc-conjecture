import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlThetaLineBundleFromCurve
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlThetaLineBundleObstruction
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceThetaDivisor

/-!
# Source theta function/line bundle: actual divisor object and named exact obligations

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
  formula (finite integer part plus real archimedean part);
* the actual q_v^(j^2) theta-value family thetaUnit / thetaQUnit of the
  analytic carrier, its power identity, nonvanishing and empty zero locus.

Not available in the tree: the theta line bundle on the source curve, the theta
object A_Theta, the theta function/global section, the identification of its
zero divisor with the {q_j^2} divisor, the q-pilot arithmetic divisor, and the
Theta-link identification.  These seven items are recorded here as named exact
obligations: a Type-valued enumeration of the exact missing source datum.
This replaces the former structure with seven Prop fields and the Nonempty
gate, which was a weak interface: its fields were free propositions, so the
gate was inhabited by (True, ...) and asserted nothing.  The named enumeration
has no propositional field, no inhabitant and no gate.

No inequality is asserted and no line bundle, theta object or theta function is
constructed or faked.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace ABCBridge.SourceThetaFunctionLineBundleActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.ThetaFieldTower
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

/-! ## Named exact obligations

The seven paper items that the source contract does not supply.  Each item is a
named constructor of the enumeration below; there is no propositional field and
no gate.  The items are exact because they are the seven paper objects and
identities listed in the module docstring, not free propositions that the
caller may instantiate by True. -/

/-- The seven exact missing theta-function/line-bundle obligations, named:

1. curveLineBundle: a theta line bundle on the actual source arithmetic curve;
2. thetaObject: the theta object A_Theta;
3. thetaFunction: the theta function (the etale theta function of IUT II);
4. thetaGlobalSection: its global section (the theta line-bundle section);
5. thetaZeroDivisorEq: the identification of the theta section zero divisor
   with the {q_j^2} divisor;
6. qPilotDivisor: the q-pilot arithmetic divisor determined by the q_v;
7. thetaLinkIdentification: the Theta-link identification.

The enumeration is Type-valued bookkeeping of the exact missing source datum.
No constructor is inhabited by this file: it does not construct a line bundle,
a theta object, a theta function, a divisor identification or a link. -/
inductive ThetaFunctionLineBundleObligation : Type
  | curveLineBundle
  | thetaObject
  | thetaFunction
  | thetaGlobalSection
  | thetaZeroDivisorEq
  | qPilotDivisor
  | thetaLinkIdentification
  deriving DecidableEq, Repr

/-- The exact list of the seven missing theta-function/line-bundle obligations. -/
def thetaFunctionLineBundleObligations
    (S : SourceDefinition31Data.{u} l) :
    List ThetaFunctionLineBundleObligation :=
  [ .curveLineBundle,
    .thetaObject,
    .thetaFunction,
    .thetaGlobalSection,
    .thetaZeroDivisorEq,
    .qPilotDivisor,
    .thetaLinkIdentification ]

/-- Exactly seven named obligations are missing. -/
theorem thetaFunctionLineBundleObligations_length
    (S : SourceDefinition31Data.{u} l) :
    (thetaFunctionLineBundleObligations (l := l) S).length = 7 := rfl

/-- The missing list is exactly the seven named obligations. -/
theorem thetaFunctionLineBundleObligations_eq
    (S : SourceDefinition31Data.{u} l) :
    (thetaFunctionLineBundleObligations (l := l) S) =
      [ .curveLineBundle,
        .thetaObject,
        .thetaFunction,
        .thetaGlobalSection,
        .thetaZeroDivisorEq,
        .qPilotDivisor,
        .thetaLinkIdentification ] := rfl

/-- The type of the exact outstanding obligations: the list of the seven named
missing items.  Downstream consumers hold this list directly; it is not a
propositional assumption and cannot be used to manufacture an object. -/
abbrev ThetaFunctionLineBundleObligations
    (S : SourceDefinition31Data.{u} l) : Type :=
  List ThetaFunctionLineBundleObligation

/-- The exact outstanding obligations of the source. -/
def actualThetaFunctionLineBundleObligations
    (S : SourceDefinition31Data.{u} l) :
    ThetaFunctionLineBundleObligations (l := l) S :=
  thetaFunctionLineBundleObligations (l := l) S

/-- Actually seven obligations are outstanding. -/
theorem actualThetaFunctionLineBundleObligations_length
    (S : SourceDefinition31Data.{u} l) :
    (actualThetaFunctionLineBundleObligations (l := l) S).length = 7 := rfl

/-- The available object is divisor-level only; it does not contain a theta
line bundle, theta function, or the {q_j^2} global zero divisor.  The seven
named obligations are exactly the missing source datum. -/
theorem thetaFunctionLineBundle_available_is_divisor_only :
    actualThetaDivisorType S =
        (NumberField.InfinitePlace S.arithmetic.F → ℤ) ∧
      actualThetaDivisorDegree S (actualThetaZeroDivisor S) = 0 ∧
      (thetaFunctionLineBundleObligations (l := l) S).length = 7 :=
  ⟨sourceThetaLineBundleDivisorType_eq S,
    sourceThetaLineBundleZeroDivisor_degree S,
    thetaFunctionLineBundleObligations_length (l := l) S⟩

end ABCBridge.SourceThetaFunctionLineBundleActual

end
