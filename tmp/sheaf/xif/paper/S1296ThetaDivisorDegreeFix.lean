import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlThetaObjectActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36ProductFormula
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

/-!
# Actual weighted-degree and Galois-invariance for source theta divisors

This file proves, for an actual Definition 3.1 source S:

* the weighted-degree formula for an arbitrary SourceThetaDivisor S;
* additivity/negation of the weighted degree;
* the exact Galois-invariance predicate and closure of invariant divisors under
  zero, addition, negation and subtraction;
* the zero-divisor degree and invariance;
* the actual product-formula degree-zero statement for a global unit, using the
  real finite + archimedean principal divisor (the integer SourceThetaDivisor S
  alone cannot represent the archimedean real logarithms);
* the exact six missing theta-structure items, stated without construction.

No fake theta structure, theta object, unit comparison or deck action is
introduced.  No theta spec, rank, or cardinal claim is used.
-/

namespace ABCBridge.SourceQlThetaDivisorDegreeActual

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.InfinitePlacePsiCnsResidual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.PrimeStripProductFormula
open ABCBridge.SourceQlThetaObjectActual
open scoped BigOperators

universe u

variable {l : LeanFormal.IUT.PrimeGeFive}
variable (S : SourceDefinition31Data.{u} l)

/-- The weighted degree formula for an arbitrary source theta divisor. -/
theorem sourceQlThetaDivisorDegreeActual_formula
    (D : SourceThetaDivisor S) :
    sourceThetaDegree S D =
      ∑ w : NumberField.InfinitePlace S.arithmetic.F,
        (NumberField.InfinitePlace.mult w : ℤ) * D w :=
  rfl

/-- The weighted degree is additive. -/
theorem sourceQlThetaDivisorDegreeActual_add
    (D E : SourceThetaDivisor S) :
    sourceThetaDegree S (D + E) =
      sourceThetaDegree S D + sourceThetaDegree S E := by
  simp [sourceThetaDegree, Finset.sum_add_distrib, mul_add]

/-- The weighted degree changes sign under negation. -/
theorem sourceQlThetaDivisorDegreeActual_neg
    (D : SourceThetaDivisor S) :
    sourceThetaDegree S (-D) = -sourceThetaDegree S D := by
  simp [sourceThetaDegree, Finset.sum_neg_distrib, mul_neg]

/-- The weighted degree of subtraction. -/
theorem sourceQlThetaDivisorDegreeActual_sub
    (D E : SourceThetaDivisor S) :
    sourceThetaDegree S (D - E) =
      sourceThetaDegree S D - sourceThetaDegree S E := by
  rw [sub_eq_add_neg, sourceQlThetaDivisorDegreeActual_add,
    sourceQlThetaDivisorDegreeActual_neg]
  ring

/-- The exact Galois-invariance predicate, restated. -/
theorem sourceQlThetaDivisorDegreeActual_galois_iff
    (D : SourceThetaDivisor S) :
    sourceGaloisInvariant S D ↔
      ∀ σ : S.arithmetic.F ≃ₐ[S.arithmetic.Fmod] S.arithmetic.F,
        ∀ w : NumberField.InfinitePlace S.arithmetic.F,
          D (w.comap σ.toRingHom) = D w :=
  Iff.rfl

/-- The zero divisor is Galois invariant. -/
theorem sourceQlThetaDivisorDegreeActual_galois_zero :
    sourceGaloisInvariant S (0 : SourceThetaDivisor S) := by
  intro σ w
  rfl

/-- The sum of two Galois-invariant divisors is Galois invariant. -/
theorem sourceQlThetaDivisorDegreeActual_galois_add
    {D E : SourceThetaDivisor S}
    (hD : sourceGaloisInvariant S D)
    (hE : sourceGaloisInvariant S E) :
    sourceGaloisInvariant S (D + E) := by
  intro σ w
  change D (w.comap σ.toRingHom) + E (w.comap σ.toRingHom) = D w + E w
  rw [hD σ w, hE σ w]

/-- The negation of a Galois-invariant divisor is Galois invariant. -/
theorem sourceQlThetaDivisorDegreeActual_galois_neg
    {D : SourceThetaDivisor S}
    (hD : sourceGaloisInvariant S D) :
    sourceGaloisInvariant S (-D) := by
  intro σ w
  change -(D (w.comap σ.toRingHom)) = -(D w)
  rw [hD σ w]

/-- The difference of two Galois-invariant divisors is Galois invariant. -/
theorem sourceQlThetaDivisorDegreeActual_galois_sub
    {D E : SourceThetaDivisor S}
    (hD : sourceGaloisInvariant S D)
    (hE : sourceGaloisInvariant S E) :
    sourceGaloisInvariant S (D - E) := by
  intro σ w
  change D (w.comap σ.toRingHom) - E (w.comap σ.toRingHom) = D w - E w
  rw [hD σ w, hE σ w]

/-- The zero divisor has degree zero. -/
theorem sourceQlThetaDivisorDegreeActual_zero_degree :
    sourceThetaDegree S (0 : SourceThetaDivisor S) = 0 := by
  simp [sourceThetaDegree]

/-- The actual zero divisor from the source object package. -/
theorem sourceQlThetaDivisorDegreeActual_zeroDivisor :
    sourceThetaDegree S (sourceThetaObjectZeroDivisor S) = 0 :=
  sourceThetaObjectZeroDivisor_degree S

/-- The actual zero divisor is Galois invariant. -/
theorem sourceQlThetaDivisorDegreeActual_zeroDivisor_galois :
    sourceGaloisInvariant S (sourceThetaObjectZeroDivisor S) :=
  sourceThetaObjectZeroDivisor_galois S

/-! ## Principal divisor degree zero

The integer source theta divisor is a function on infinite places only.  The
actual principal divisor of a global unit has an integer finite part and a real
archimedean part -log(w f); the product formula states that the total weighted
degree (finite + archimedean) is zero.  We state exactly this actual real-valued
principal degree.  No integer infinite-place principal divisor is invented. -/

/-- The actual finite principal-divisor degree of a global unit. -/
noncomputable def sourcePrincipalFiniteDegree
    (f : S.arithmetic.Fˣ) : ℝ :=
  (principalDivisorFinite f).sum (fun v n =>
    (n : ℝ) * Real.log ((finitePlaceResidueCardinality (F := S.arithmetic.F) v : ℝ)))

/-- The actual archimedean principal-divisor degree of a global unit. -/
noncomputable def sourcePrincipalArchimedeanDegree
    (f : S.arithmetic.Fˣ) : ℝ :=
  ∑ w : NumberField.InfinitePlace S.arithmetic.F,
    (NumberField.InfinitePlace.mult w : ℝ) * archimedeanPlaceValue w f

/-- The actual total principal-divisor degree of a global unit. -/
noncomputable def sourcePrincipalTotalDegree
    (f : S.arithmetic.Fˣ) : ℝ :=
  sourcePrincipalFiniteDegree S f + sourcePrincipalArchimedeanDegree S f

/-- Actual product formula: the total principal-divisor degree of a global unit
is zero. -/
theorem sourcePrincipalTotalDegree_zero
    (f : S.arithmetic.Fˣ) :
    sourcePrincipalTotalDegree S f = 0 := by
  unfold sourcePrincipalTotalDegree sourcePrincipalFiniteDegree
    sourcePrincipalArchimedeanDegree
  exact productFormula_finsupp (F := S.arithmetic.F) f

/-- The archimedean principal function of a global unit, as an actual real-valued
function on the infinite places. -/
noncomputable def sourcePrincipalInfiniteFunction
    (f : S.arithmetic.Fˣ) :
    NumberField.InfinitePlace S.arithmetic.F → ℝ :=
  principalDivisorInfinite f

/-- Its real weighted degree is the archimedean principal degree. -/
theorem sourcePrincipalInfiniteFunction_degree
    (f : S.arithmetic.Fˣ) :
    (∑ w : NumberField.InfinitePlace S.arithmetic.F,
      (NumberField.InfinitePlace.mult w : ℝ) *
        sourcePrincipalInfiniteFunction S f w) =
      sourcePrincipalArchimedeanDegree S f :=
  rfl

/-- The exact integer-divisor boundary: the integer source theta divisor cannot
represent the real archimedean principal divisor.  This theorem records the
available two-part real degree formula without asserting an integer principal
divisor on infinite places. -/
theorem sourceQlThetaDivisorDegreeActual_principalBoundary
    (f : S.arithmetic.Fˣ) :
    sourcePrincipalFiniteDegree S f +
        sourcePrincipalArchimedeanDegree S f = 0
      ∧ sourceThetaDegree S (0 : SourceThetaDivisor S) = 0 :=
  ⟨sourcePrincipalTotalDegree_zero S f,
    sourceQlThetaDivisorDegreeActual_zero_degree S⟩

/-- The exact six missing theta-structure items (documentation and bookkeeping
only; no object or inhabitant is constructed). -/
theorem sourceQlThetaDivisorDegreeActual_missingData_length :
    (sourceThetaObjectMissingData S).length = 6 :=
  sourceThetaObjectMissingData_length S

/-- Exact residual: arbitrary-divisor degree formula, Galois closure, zero
divisor degree, actual real principal degree zero, and the six missing items. -/
theorem sourceQlThetaDivisorDegreeActual_exactResidual :
    (∀ D : SourceThetaDivisor S,
      sourceThetaDegree S D =
        ∑ w : NumberField.InfinitePlace S.arithmetic.F,
          (NumberField.InfinitePlace.mult w : ℤ) * D w)
      ∧
    (∀ D E : SourceThetaDivisor S,
      sourceThetaDegree S (D + E) =
        sourceThetaDegree S D + sourceThetaDegree S E)
      ∧
    sourceThetaDegree S (sourceThetaObjectZeroDivisor S) = 0
      ∧
    (sourceGaloisInvariant S (0 : SourceThetaDivisor S))
      ∧
    (∀ f : S.arithmetic.Fˣ,
      sourcePrincipalFiniteDegree S f +
        sourcePrincipalArchimedeanDegree S f = 0)
      ∧
    (sourceThetaObjectMissingData S).length = 6 :=
  ⟨sourceQlThetaDivisorDegreeActual_formula S,
    sourceQlThetaDivisorDegreeActual_add S,
    sourceQlThetaDivisorDegreeActual_zeroDivisor S,
    sourceQlThetaDivisorDegreeActual_galois_zero S,
    sourcePrincipalTotalDegree_zero S,
    sourceThetaObjectMissingData_length S⟩

/-- The actual degree theorem is for the integer source divisor type; the
principal degree-zero theorem is the real finite + archimedean product formula.
No integer principal divisor on infinite places is asserted. -/
theorem sourceQlThetaDivisorDegreeActual_scope :
    (∀ D : SourceThetaDivisor S,
      sourceThetaDegree S D =
        ∑ w : NumberField.InfinitePlace S.arithmetic.F,
          (NumberField.InfinitePlace.mult w : ℤ) * D w)
      ∧
    (∀ f : S.arithmetic.Fˣ,
      sourcePrincipalFiniteDegree S f +
        sourcePrincipalArchimedeanDegree S f = 0) :=
  ⟨sourceQlThetaDivisorDegreeActual_formula S,
    sourcePrincipalTotalDegree_zero S⟩

/-- The actual zero divisor is an integer source divisor with degree zero and
Galois invariance; this packages both available facts. -/
theorem sourceQlThetaDivisorDegreeActual_zeroDivisor_package :
    sourceThetaDegree S (sourceThetaObjectZeroDivisor S) = 0
      ∧ sourceGaloisInvariant S (sourceThetaObjectZeroDivisor S) :=
  ⟨sourceThetaObjectZeroDivisor_degree S,
    sourceThetaObjectZeroDivisor_galois S⟩

/-- The actual principal-divisor real degree has its finite and archimedean
components exposed separately. -/
theorem sourceQlThetaDivisorDegreeActual_principal_components
    (f : S.arithmetic.Fˣ) :
    sourcePrincipalTotalDegree S f =
      sourcePrincipalFiniteDegree S f +
        sourcePrincipalArchimedeanDegree S f :=
  rfl

/-- The integer divisor degree and the real principal degree are separate; the
latter is zero by the product formula. -/
theorem sourceQlThetaDivisorDegreeActual_twoDegrees :
    (sourceThetaDegree S (0 : SourceThetaDivisor S) = 0)
      ∧
    (∀ f : S.arithmetic.Fˣ,
      sourcePrincipalFiniteDegree S f +
        sourcePrincipalArchimedeanDegree S f = 0) :=
  ⟨sourceQlThetaDivisorDegreeActual_zero_degree S,
    sourcePrincipalTotalDegree_zero S⟩


end

end ABCBridge.SourceQlThetaDivisorDegreeActual
