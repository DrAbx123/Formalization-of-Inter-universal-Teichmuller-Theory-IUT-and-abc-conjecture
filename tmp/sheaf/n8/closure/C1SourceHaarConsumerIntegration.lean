import tmp.sheaf.n8.closure.C1SourceHaarActualPath
import tmp.sheaf.n8.closure.C1NativeConsumerPaperRoute
import tmp.sheaf.n8.closure.C1QuotientFiberData

/-!
# C1 sourceHaar consumer integration into the paper/N8 C1 layer

The zero-sorry sourceHaar actual path (C1SourceHaarActualPath) is connected to
the native paper-route C1 layer (C1NativeConsumerPaperRoute) by an external
adapter.  Both components are actual:

- sourceHaar side: sourceHaarActualOriginalInput / sourceHaarActualImageRealization
  over V = Unit with q = 1, plus the actual C1PlaceQuotientFiberData quotient
  target;
- native side: NativeC1PaperRoute X, the actual native place/selected data plus
  the actual quotient target.

This is deliberately an external package: PaperN8Output/N8RouteObligations have
no C1 slot, so no route-level compatibility relation is invented.

The old SourceInputBinding over V = Unit remains rejected: Unit is a
subsingleton, so it cannot be equivalent to a nontrivial number-field place
index (see C1SourceHaarActualPath).  The corrected sourceHaar consumer avoids
that old equivalence.  No arbitrary V/equivalence is introduced.

Arithmetic compatibility between an arbitrary sourceHaar datum S and a native
input X is only available under an explicit equality of their Fmod roots; the
conditional structure below records that exact bridge rather than choosing one.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1SourceHaarConsumerIntegration

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C1NativeConsumerPaperRoute
open LeanFormal.IUT.N8Closure.C1SourceHaarActualPath
open LeanFormal.IUT.N8Closure.C1QuotientFiberData
open LeanFormal.IUT.Theorem311Source

variable {l : PrimeGeFive}

/-- Actual sourceHaar C1 paper consumer: the zero-sorry sourceHaar corrected
consumer with its actual quotient target exposed. -/
structure SourceHaarC1PaperConsumer (S : SourceDefinition31Data.{0} l) where
  consumer : SourceHaarActualCorrectedConsumer S
  quotient : C1PlaceQuotientFiberData (F := S.arithmetic.Fmod)
  quotient_eq : quotient = consumer.quotientTarget

/-- Actual construction of the sourceHaar C1 paper consumer. -/
noncomputable def sourceHaarC1PaperConsumer (S : SourceDefinition31Data.{0} l) :
    SourceHaarC1PaperConsumer S where
  consumer := sourceHaarActualCorrectedConsumer S
  quotient := c1PlaceQuotientFiberData (F := S.arithmetic.Fmod)
  quotient_eq := rfl

theorem sourceHaarC1PaperConsumer_nonempty
    (S : SourceDefinition31Data.{0} l) :
    Nonempty (SourceHaarC1PaperConsumer S) :=
  ⟨sourceHaarC1PaperConsumer S⟩

/-- Actual external integration of the sourceHaar C1 consumer and the native
paper-route C1 layer.  No compatibility field is invented; the structure just
packages two actual objects over their own inputs. -/
structure SourceHaarNativeC1Integration
    (S : SourceDefinition31Data.{0} l) (X : N8NativeInput l) where
  sourceHaar : SourceHaarC1PaperConsumer S
  nativeRoute : NativeC1PaperRoute X

/-- Actual external integration, from the two actual layer constructors. -/
noncomputable def sourceHaarNativeC1Integration
    (S : SourceDefinition31Data.{0} l) (X : N8NativeInput l) :
    SourceHaarNativeC1Integration S X where
  sourceHaar := sourceHaarC1PaperConsumer S
  nativeRoute := nativeC1PaperRoute X

theorem sourceHaarNativeC1Integration_nonempty
    (S : SourceDefinition31Data.{0} l) (X : N8NativeInput l) :
    Nonempty (SourceHaarNativeC1Integration S X) :=
  ⟨sourceHaarNativeC1Integration S X⟩

/-- Exact arithmetic bridge needed for genuine compatibility of the two C1
layers.  It is not chosen by this file. -/
def SourceHaarNativeArithmeticBridge
    (S : SourceDefinition31Data.{0} l) (X : N8NativeInput l) : Prop :=
  S.arithmetic.Fmod = X.S.arithmetic.Fmod

/-- Conditional compatibility of the two C1 layers, under an explicit Fmod
equality.  The equality is an input, not an arbitrary equivalence. -/
structure SourceHaarNativeC1Compatibility
    (S : SourceDefinition31Data.{0} l) (X : N8NativeInput l)
    (h : SourceHaarNativeArithmeticBridge S X) where
  integration : SourceHaarNativeC1Integration S X
  arithmetic_eq : SourceHaarNativeArithmeticBridge S X

/-- Conditional actual compatibility from the bridge equality. -/
noncomputable def sourceHaarNativeC1CompatibilityOfEq
    (S : SourceDefinition31Data.{0} l) (X : N8NativeInput l)
    (h : SourceHaarNativeArithmeticBridge S X) :
    SourceHaarNativeC1Compatibility S X h where
  integration := sourceHaarNativeC1Integration S X
  arithmetic_eq := h

theorem sourceHaarNativeC1Compatibility_nonempty_of_eq
    (S : SourceDefinition31Data.{0} l) (X : N8NativeInput l)
    (h : SourceHaarNativeArithmeticBridge S X) :
    Nonempty (SourceHaarNativeC1Compatibility S X h) :=
  ⟨sourceHaarNativeC1CompatibilityOfEq S X h⟩

/-- Decisive target correction: without the explicit arithmetic bridge the two
C1 layers remain parallel actual layers; no route-level C1 slot or arbitrary
identification is asserted. -/
def SourceHaarNativeC1TargetCorrection
    (S : SourceDefinition31Data.{0} l) (X : N8NativeInput l) : Prop :=
  SourceHaarNativeArithmeticBridge S X

end LeanFormal.IUT.N8Closure.C1SourceHaarConsumerIntegration
