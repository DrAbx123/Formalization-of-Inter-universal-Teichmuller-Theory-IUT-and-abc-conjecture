import tmp.sheaf.xif.paper.S3030AffineOriginClassification
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3030AffineOriginClassification
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3036IsDomainR0
local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

abbrev R0 : Type := S2801E37CoordinateRing S2844D6F6BaseChangeActual.K
abbrev x : R0 := S2801E37X S2844D6F6BaseChangeActual.K
abbrev y : R0 := S2801E37Y S2844D6F6BaseChangeActual.K

/-- Target: R0 is a domain. -/
def S3036R0IsDomain : Prop := IsDomain R0

/-- Actual transport: a ring equivalence from R0 to a domain makes R0 a domain. -/
theorem S3036_domain_of_equiv
    {A : Type} [Semiring A] [IsDomain A] (e : R0 ≃+* A) : IsDomain R0 :=
  MulEquiv.isDomain A e.toMulEquiv

/-- Mathlib's actual domain instance for the Weierstrass affine coordinate ring. -/
noncomputable abbrev S3036MathlibRing : Type :=
  (S2801E37Curve S2844D6F6BaseChangeActual.K).toAffine.CoordinateRing

theorem S3036_mathlib_domain : IsDomain S3036MathlibRing :=
  inferInstance

/-- Exact bridge target: R0 is ring-equivalent to Mathlib's Weierstrass affine
coordinate ring. -/
def S3036BridgeTarget : Prop := Nonempty (R0 ≃+* S3036MathlibRing)

/-- Conditional domain proof via the bridge. -/
theorem S3036_domain_of_bridge (h : S3036BridgeTarget) : IsDomain R0 := by
  rcases h with ⟨e⟩
  exact S3036_domain_of_equiv e

/-!
## First error

S3036R0IsDomain is not proved directly.  Mathlib has the actual domain instance
for (S2801E37Curve K).toAffine.CoordinateRing, and S3036_domain_of_equiv
transports a ring equivalence.  The missing object is exactly S3036BridgeTarget:
a ring equivalence between R0 = K[x,y]/(y^2+y-x^3+x) as constructed in
S2801D6FaithfulActual and Mathlib's AdjoinRoot coordinate ring.  No domain proof
is faked.
-/

#check S3036R0IsDomain
#check S3036_domain_of_equiv
#check S3036MathlibRing
#check S3036_mathlib_domain
#check S3036BridgeTarget
#check S3036_domain_of_bridge
#print axioms S3036_mathlib_domain
#print axioms S3036_domain_of_bridge

end LeanFormal.IUT.XiFPaper.S3036IsDomainR0
end
