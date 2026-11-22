import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlThetaLineBundleFromCurve
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlThetaDivisorDegreeActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceThetaDivisor
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceThetaGenerator

/-! # S1384: theta line bundle from actual curve/divisor/theta packet donors

Actual donors available in the tree:
* the source arithmetic punctured elliptic curve and Weierstrass model;
* the source theta-divisor type and its weighted degree / zero divisor;
* the actual theta-value family thetaUnit t j = q_v^(j^2);
* the odd theta q-series order-zero analysis (Example36SourceThetaDivisor).

EXACT FIRST MISSING FIELD (not constructed, not faked):
there is no line-bundle carrier on `sourceThetaLineBundleCurve S` in the tree.
Consequently there is no theta global section, no identification of its zero
divisor with the {q_j^2} divisor, no q-pilot arithmetic divisor, and no
Theta-link.  The first required object is:
  a line-bundle object L on the source punctured elliptic curve together with
  a global section theta whose zero divisor is the {q_j^2} divisor.
No `Nonempty` gate, no Prop-field package, and no arbitrary carrier is
introduced here.
-/

noncomputable section

namespace ABCBridge.S1384ThetaLineBundleActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaGenerator
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaDivisor
open ABCBridge.SourceQlThetaLineBundleFromCurve
open ABCBridge.SourceQlThetaDivisorDegreeActual

universe u

variable {l : PrimeGeFive}
variable (S : SourceDefinition31Data.{u} l)

/-- Actual source punctured elliptic curve. -/
abbrev s1384Curve : PuncturedEllipticCurve S.arithmetic.F :=
  sourceThetaLineBundleCurve S

/-- Actual source Weierstrass model. -/
abbrev s1384Weierstrass : WeierstrassCurve S.arithmetic.F :=
  sourceThetaLineBundleWeierstrass S

/-- Actual source theta-divisor type. -/
abbrev s1384DivisorType (S : SourceDefinition31Data.{u} l) : Type u :=
  sourceThetaLineBundleDivisorType S

/-- Actual weighted degree on the source divisor type. -/
abbrev s1384Degree (S : SourceDefinition31Data.{u} l) :
    s1384DivisorType S → ℤ :=
  sourceThetaLineBundleDegree S

/-- Actual zero theta divisor. -/
noncomputable def s1384ZeroDivisor (S : SourceDefinition31Data.{u} l) :
    s1384DivisorType S :=
  sourceThetaLineBundleZeroDivisor S

/-- The actual zero divisor has degree zero. -/
theorem s1384ZeroDivisor_degree (S : SourceDefinition31Data.{u} l) :
    s1384Degree S (s1384ZeroDivisor S) = 0 :=
  sourceThetaLineBundleZeroDivisor_degree S

/-- Actual theta-value family q_v^(j^2), from the analytic theta packet. -/
noncomputable def s1384ThetaValueFamily (t : AnalyticThetaCarrier) :
    SignedLabel l.value → ℝˣ :=
  fun j => thetaUnit t j.1

/-- The theta value at j is the q_v^(j^2) power. -/
theorem s1384ThetaValueFamily_pow (t : AnalyticThetaCarrier)
    (j : SignedLabel l.value) :
    s1384ThetaValueFamily (l := l) t j =
      thetaQUnit t ^ (gaussExponent j.1).toNat := by
  exact thetaUnit_eq_qUnit_pow t j.1

/-- The actual analytic theta value is nonzero. -/
theorem s1384ThetaValueFamily_ne_zero (t : AnalyticThetaCarrier)
    (j : SignedLabel l.value) :
    ((s1384ThetaValueFamily (l := l) t j : ℝ)) ≠ 0 := by
  have hpos : (0 : ℝ) < (thetaUnit t j.1 : ℝ) := by
    rw [thetaUnit_apply]
    exact realThetaValue_pos t.q_pos j.1
  exact ne_of_gt hpos

end ABCBridge.S1384ThetaLineBundleActual

end
