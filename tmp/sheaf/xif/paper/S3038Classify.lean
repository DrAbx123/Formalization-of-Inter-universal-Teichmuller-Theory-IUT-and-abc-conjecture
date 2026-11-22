import tmp.sheaf.xif.paper.S3037Factorization
import tmp.sheaf.xif.paper.S3036IsDomainR0

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

namespace LeanFormal.IUT.XiFPaper.S3038Classify
local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

abbrev R0 : Type := S2801E37CoordinateRing S2844D6F6BaseChangeActual.K
abbrev x : R0 := S2801E37X S2844D6F6BaseChangeActual.K
abbrev y : R0 := S2801E37Y S2844D6F6BaseChangeActual.K


/-- Actual Y-classification from domain + factorization: if φ fixes x and R0 is
a domain, then φ(y) = y or φ(y) = -1 - y. -/
theorem S3038_fixesY_or_alpha (hdom : IsDomain R0) (φ : R0 →+* R0) (hx : φ x = x) :
    φ y = y ∨ φ y = -1 - y := by
  have hfac := S3037Factorization.S3037_factorization φ hx
  rcases mul_eq_zero.mp hfac with hzero | hzero
  · left
    linear_combination hzero
  · right
    linear_combination hzero

/-- Generation input: a ring endomorphism of R0 fixing both x and y is the
identity. -/
def S3038GeneratedByXY : Prop :=
  ∀ ψ : R0 →+* R0, ψ x = x → ψ y = y → ψ = RingHom.id R0

/-- Conditional id-or-alpha classification from domain, generation, and the
actual Y-classification. -/
theorem S3038_id_or_alpha
    (hdom : IsDomain R0) (hgen : S3038GeneratedByXY)
    (φ : R0 →+* R0) (hx : φ x = x)
    (hφ2 : φ.comp φ = RingHom.id R0)
    (halpha : φ y = -1 - y → φ = S2853RingHom S2844D6F6BaseChangeActual.K) :
    φ = RingHom.id R0 ∨ φ = S2853RingHom S2844D6F6BaseChangeActual.K := by
  rcases S3038_fixesY_or_alpha hdom φ hx with hy | hy
  · left
    apply hgen φ hx hy
  · right
    exact halpha hy

/-!
## Exact target and first error

S3038_fixesY_or_alpha is actual: the factorization
(φ y - y)(φ y + y + 1)=0 plus IsDomain R0 gives φ y = y or φ y = -1 - y.

The remaining missing inputs for the full classification are:
* S3036R0IsDomain (or the bridge to Mathlib's coordinate ring);
* S3038GeneratedByXY: X,Y generate R0, so a ring hom is determined by their
  images.  This is the same rank-two/normal-form input as S3035NormalForm;
* matching φ(y) = -1-y to the actual alpha ring hom S2853RingHom (the chart-Z
  substitution), which is exactly the polynomial computation on generators.

The second branch uses the explicit input halpha (generator uniqueness for the
chart-Z substitution); no full classification is asserted as proved.
-/

#check S3038_fixesY_or_alpha
#check S3038GeneratedByXY
#check S3038_id_or_alpha
#print axioms S3038_fixesY_or_alpha

end LeanFormal.IUT.XiFPaper.S3038Classify
end
