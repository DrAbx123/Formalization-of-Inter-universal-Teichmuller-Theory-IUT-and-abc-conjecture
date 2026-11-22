import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Scheme
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlThetaLineBundleFromCurve
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlThetaDivisorDegreeActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceThetaDivisor
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceThetaGenerator

/-! # S1401: Mathlib line-bundle/Picard route to the source theta line bundle

Actual donors used:
* the source punctured elliptic curve and Weierstrass model;
* the affine coordinate ring WeierstrassCurve.Affine.CoordinateRing of the
  source Weierstrass model and its spectrum scheme;
* the source theta-divisor type/degree/zero divisor;
* the actual theta-value family q_v^(j^2).

EXACT FIRST MISSING FIELD (no fake, no Nonempty/Prop gate):
there is no line-bundle object on the source curve in the tree, and no theta
global section.  Mathlib supplies Scheme and WeierstrassCurve.Affine.
CoordinateRing, but the theta line bundle, its global section, the
zero-divisor equality with {q_j^2}, the q-pilot divisor and the Theta-link are
not constructed.  The first required datum is a line bundle L on the source
curve plus a global section theta with the prescribed zero divisor.
-/

noncomputable section

namespace ABCBridge.S1401ThetaLineBundleActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open AlgebraicGeometry
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaGenerator
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaDivisor
open ABCBridge.SourceQlThetaLineBundleFromCurve
open ABCBridge.SourceQlThetaDivisorDegreeActual
open WeierstrassCurve

universe u

variable {l : PrimeGeFive}
variable (S : LeanFormal.IUT.Theorem311Source.SourceDefinition31Data.{u} l)

/-- Actual affine coordinate ring of the source Weierstrass model. -/
abbrev s1401CoordinateRing (S : LeanFormal.IUT.Theorem311Source.SourceDefinition31Data.{u} l) : Type u :=
  Affine.CoordinateRing (S.arithmetic.curve.curve.toAffine)

/-- Actual affine scheme of the source Weierstrass model (Mathlib Spec). -/
abbrev s1401AffineScheme (S : LeanFormal.IUT.Theorem311Source.SourceDefinition31Data.{u} l) : Scheme.{u} :=
  Spec (CommRingCat.of (s1401CoordinateRing S))

/-- Actual source punctured elliptic curve. -/
abbrev s1401Curve : PuncturedEllipticCurve S.arithmetic.F :=
  sourceThetaLineBundleCurve S

/-- Actual source theta-divisor type. -/
abbrev s1401DivisorType (S : LeanFormal.IUT.Theorem311Source.SourceDefinition31Data.{u} l) : Type u :=
  sourceThetaLineBundleDivisorType S

/-- Actual weighted theta degree. -/
abbrev s1401Degree (S : LeanFormal.IUT.Theorem311Source.SourceDefinition31Data.{u} l) :
    s1401DivisorType S → ℤ :=
  sourceThetaLineBundleDegree S

/-- Actual zero theta divisor. -/
noncomputable def s1401ZeroDivisor (S : LeanFormal.IUT.Theorem311Source.SourceDefinition31Data.{u} l) :
    s1401DivisorType S :=
  sourceThetaLineBundleZeroDivisor S

theorem s1401ZeroDivisor_degree (S : LeanFormal.IUT.Theorem311Source.SourceDefinition31Data.{u} l) :
    s1401Degree S (s1401ZeroDivisor S) = 0 :=
  sourceThetaLineBundleZeroDivisor_degree S

/-- Actual theta-value family q_v^(j^2). -/
noncomputable def s1401ThetaValueFamily (t : AnalyticThetaCarrier) :
    SignedLabel l.value → ℝˣ :=
  fun j => thetaUnit t j.1

end ABCBridge.S1401ThetaLineBundleActual

end
