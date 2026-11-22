import tmp.sheaf.xif.paper.NativeQNormActual

/-! # CONDITIONAL STATUS (xi-f)

Conditional on NativeQOrderResidueBound; no production base-power/factor-2 lower bound is supplied.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-! # Native q Tate norm bound from order/residue data

NativeQNormActual reduces the target to

  nativeQLogMagnitude X = order * log (residueNormBase base).

For l = 5, if the base residue norm is 5^f and the product of the q order with
f is at least 2, then the magnitude is at least 2 log 5.  The actual source
supplies order > 0 and residueNormBase > 1, but not the base-power equality
or the product lower bound.  This file proves the conditional bound and
isolates the exact missing order/residue lower bound.

No arbitrary bound/axiom/sorry. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.NativeQTateNormProof

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaNativeQExponentActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.NativeQNormActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The exact missing order/residue data for l = 5: the base residue norm is
5^f and the product of the native q order with f is at least 2. -/
structure NativeQOrderResidueBound where
  fbase : Nat
  base_eq : residueNormBase (nativeBadBasePlace X) = (5 : Real) ^ fbase
  product_ge_two : 2 ≤ (C9QPilotRegion.nativeQ X).order * fbase

/-- Conditional proof of the Tate norm bound from the exact order/residue
lower bound. -/
theorem nativeQTateNormBound_of_orderResidue
    (D : NativeQOrderResidueBound (X := X)) :
    NativeQTateNormBound (X := X) := by
  unfold NativeQTateNormBound
  rw [nativeQLogMagnitude_eq_order_mul_log (X := X), D.base_eq, Real.log_pow]
  have hlog5 : 0 < Real.log (5 : Real) :=
    Real.log_pos (by norm_num)
  have hcast : (2 : Real) ≤
      ((C9QPilotRegion.nativeQ X).order : Real) * (D.fbase : Real) := by
    exact_mod_cast D.product_ge_two
  nlinarith

/-- The missing order/residue lower bound is exactly the gap: order > 0 and
base > 1 do not imply either the base-power equality or the factor-2 product. -/
def NativeQOrderResidueGap : Prop :=
  Nonempty (NativeQOrderResidueBound (X := X))

/-- Conditional bound: the gap package supplies NativeQTateNormBound. -/
theorem nativeQTateNormBound_of_gap
    (h : NativeQOrderResidueGap (X := X)) :
    NativeQTateNormBound (X := X) := by
  rcases h with ⟨D⟩
  exact nativeQTateNormBound_of_orderResidue (X := X) D

/-! ## Exact missing order/residue lower bound

For l = 5, the required data are:

1. fbase : Nat with
     residueNormBase (nativeBadBasePlace X) = 5 ^ fbase;
2. 2 <= order * fbase.

The source proves only order > 0 and residueNormBase > 1.  It does not provide
the base-power equality BaseResidueNormPowerTarget at p = 5, nor the product
lower bound 2 <= order * fbase.  Those are the exact missing order/residue
lower bounds; no arbitrary bound is inserted. -/

end LeanFormal.IUT.XiFPaper.NativeQTateNormProof

end
