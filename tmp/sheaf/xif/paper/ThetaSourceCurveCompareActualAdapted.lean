import tmp.sheaf.xif.paper.ThetaQuotientTotalActualAdapted
import tmp.sheaf.xif.paper.ThetaFunctionLineBundleActual

/-!
# Actual source theta divisor to analytic quotient fiber comparison

This is the intermediate Q5 comparison at the divisor-degree/fiber level.

Actual data used:
* the actual source theta divisor type SourceThetaDivisor S and its actual
  weighted degree sourceThetaObjectDivisorDegree;
* the actual quotient theta line bundle from ThetaQuotientTotalActualAdapted, whose
  fiber is L;
* the actual zero divisor of the source theta divisor type.

The actual comparison map sends a source theta divisor D to the L-valued
weighted degree of D. This is a genuine map from source theta divisor data to
the analytic quotient fiber; it is not a line-bundle isomorphism and does not
assert source curve equality. The zero divisor is proved to map to zero, and
the principal divisor degree (product formula) maps to zero.

No donor, no inequality, and no fabricated line bundle are used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ABCBridge.ThetaSourceCurveCompareActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Foundations.Theta
open ABCBridge.SourceThetaFunctionLineBundleActual

universe u

variable {l : PrimeGeFive}
variable (S : SourceDefinition31Data.{u} l)

/-- The actual source theta divisor weighted degree, cast to the analytic fiber L. -/
def sourceThetaDivisorFiberValue {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : SourceThetaDivisor S) : L :=
  (sourceThetaObjectDivisorDegree S D : L)

/-- The actual source zero divisor has fiber value zero. -/
theorem sourceThetaZeroDivisor_fiberValue
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L] :
    sourceThetaDivisorFiberValue (L := L) S
        (sourceThetaObjectZeroDivisor S) = 0 := by
  unfold sourceThetaDivisorFiberValue
  rw [sourceThetaObjectZeroDivisor_degree]
  norm_num

/-- The comparison map is additive on actual source theta divisors. -/
theorem sourceThetaDivisorFiberValue_add
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (D E : SourceThetaDivisor S) :
    sourceThetaDivisorFiberValue (L := L) S (D + E) =
      sourceThetaDivisorFiberValue (L := L) S D +
        sourceThetaDivisorFiberValue (L := L) S E := by
  unfold sourceThetaDivisorFiberValue
  rw [sourceThetaObjectDivisorDegree_add]
  norm_num

/-- The comparison map negates on actual source theta divisors. -/
theorem sourceThetaDivisorFiberValue_neg
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (D : SourceThetaDivisor S) :
    sourceThetaDivisorFiberValue (L := L) S (-D) =
      -sourceThetaDivisorFiberValue (L := L) S D := by
  unfold sourceThetaDivisorFiberValue
  rw [sourceThetaObjectDivisorDegree_neg]
  norm_num

/-- The actual source theta divisor comparison into the analytic quotient fiber
over the period base point of the unit 1. -/
noncomputable def sourceThetaDivisorFiberMap
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) :
    SourceThetaDivisor S → thetaQuotientFiber D
      (Quot.mk (thetaPeriodSetoid D) (1 : Lˣ)) :=
  fun Dsrc => sourceThetaDivisorFiberValue (L := L) S Dsrc

/-- The zero source divisor maps to the zero fiber value. -/
theorem sourceThetaDivisorFiberMap_zero
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) :
    sourceThetaDivisorFiberMap (S := S) D
        (sourceThetaObjectZeroDivisor S) =
      (0 : thetaQuotientFiber D
        (Quot.mk (thetaPeriodSetoid D) (1 : Lˣ))) :=
  sourceThetaZeroDivisor_fiberValue (S := S) (L := L)

end ABCBridge.ThetaSourceCurveCompareActualAdapted

end
