import tmp.sheaf.n8.closure.C9QPilotRegion
import tmp.sheaf.xif.paper.NativeQNormActual
import tmp.sheaf.xif.paper.ActualC3DonorFromNativeAdapted

/-! # CONDITIONAL STATUS (xi-f)

Conditional reduction to NativeOrderBaseThetaBound / NativeQTateNormBound. The source Tate/norm bound is missing; no inequality is asserted.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-!
# Actual native q / order / residue-norm-base objects and exact blockers

This file packages only the unconditional actual native objects that exist in
the tree:

* q = NativeC3.nativeQActual X at the native F-completion;
* order = (nativeQActual X).order;
* base = ArithmeticQPilotBaseChange.residueNormBase (nativeFPlaceOverBad X);

with the actual formula nativeQLogMagnitude X = order * log base.

No SignedThetaAverageLeQMagnitude judgment is made here.  In particular this
file neither asserts nor rejects that inequality; inequality judgments before
an actual unconditional C3 object exists are not meaningful.

Exact object blockers for the C3 signed comparison:

1. nativeQActual lives at the F-completion, while SourcePilotRegionDonors.q
   lives at the Fmod place nativeC3Place X.  No descent/restriction map from the
   F-completion q to the Fmod completion exists; see
   ActualC3DonorFromNativeAdapted.MissingBaseQData,
   ActualC3DonorFromNativeAdapted.MissingBaseTensorLanding, and
   ActualC3DonorFromNativeAdapted.MissingC3DonorData.
2. Consequently no actual SourcePilotRegionDonors with q = nativeQActual X is
   constructed, and no actualSignedC3 whose completion q is the native q exists.
3. No actual paperQParameter-to-native-q identification is constructed.
4. NativeQNormActual records that the Tate lower bound
   2*log5 <= nativeQLogMagnitude X is not proved by order/base positivity alone.

No toy data, PUnit, True, axiom, or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.DirectSignedComparisonActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.XiFPaper.NativeQNormActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.ArithmeticQPilotLogVolume

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual native q / order / residue-norm-base package. -/
structure NativeQOrderBaseActual where
  q : FinitePlaceQCandidate (nativeFPlaceOverBad X)
  q_eq : q = NativeC3.nativeQActual X
  order : Nat
  order_eq : order = (NativeC3.nativeQActual X).order
  order_pos : 0 < order
  base : Real
  base_eq : base = residueNormBase (nativeFPlaceOverBad X)
  base_gt_one : 1 < base
  logMagnitude : Real
  logMagnitude_eq : logMagnitude = (order : Real) * Real.log base

/-- The actual native q/order/base record, constructed from NativeC3 and the
production residue norm base. -/
noncomputable def nativeQOrderBaseActual :
    NativeQOrderBaseActual (X := X) where
  q := NativeC3.nativeQActual X
  q_eq := rfl
  order := (NativeC3.nativeQActual X).order
  order_eq := rfl
  order_pos := (NativeC3.nativeQActual X).order_pos
  base := residueNormBase (nativeFPlaceOverBad X)
  base_eq := rfl
  base_gt_one := residueNormBase_gt_one (nativeFPlaceOverBad X)
  logMagnitude := nativeQLogMagnitude X
  logMagnitude_eq := nativeQLogMagnitude_eq_order_mul_log (X := X)

/-- The actual base-value formula, restated for the record. -/
theorem nativeQOrderBaseActual_logMagnitude_eq :
    (nativeQOrderBaseActual (X := X)).logMagnitude =
      ((nativeQOrderBaseActual (X := X)).order : Real) *
        Real.log (nativeQOrderBaseActual (X := X)).base :=
  (nativeQOrderBaseActual (X := X)).logMagnitude_eq

/-- The actual log magnitude is exactly the native q-pilot magnitude. -/
theorem nativeQOrderBaseActual_logMagnitude_eq_native :
    (nativeQOrderBaseActual (X := X)).logMagnitude =
      nativeQLogMagnitude X :=
  rfl

/-- The actual order is positive. -/
theorem nativeQOrderBaseActual_order_pos :
    0 < (nativeQOrderBaseActual (X := X)).order :=
  (nativeQOrderBaseActual (X := X)).order_pos

/-- The actual residue-norm base is strictly greater than one. -/
theorem nativeQOrderBaseActual_base_gt_one :
    1 < (nativeQOrderBaseActual (X := X)).base :=
  (nativeQOrderBaseActual (X := X)).base_gt_one

/-- The actual q at the native F-completion. -/
theorem nativeQOrderBaseActual_q_eq :
    (nativeQOrderBaseActual (X := X)).q = NativeC3.nativeQActual X :=
  (nativeQOrderBaseActual (X := X)).q_eq

end LeanFormal.IUT.XiFPaper.DirectSignedComparisonActualAdapted

end
