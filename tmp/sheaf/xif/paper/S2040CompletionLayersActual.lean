import tmp.sheaf.xif.paper.S2040CompletionBridgeS2055Actual

/-! # S2040 completion bridge layers: (1) qV completion ring, (2) integral units, (3) norm

Splits the exact missing `S2040CompletionBridgeRequired` into the three layers
requested by the task.  No carrier is duplicated: the integral-units target is
the canonical `S2055CompletionIntegralUnits`, and the norm bridge is the canonical
`S2046NormBridge`.  No inhabitant of the qV completion equivalence is asserted;
the completion at `qVPlace T b` is a finite extension of Q_p and is not generally
identified with Q_p. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2040CompletionLayersActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.S2055CompletionIntegralUnitsActual
open LeanFormal.IUT.XiFPaper.S2046CompletionOUnitsActual
open LeanFormal.IUT.XiFPaper.S2040CompletionBridgeS2055Actual
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

universe u

/-- Layer (1): the qVPlace completion ring is equivalent to a rational
completion QPlace v. -/
structure S2040QVCompletionRingEquivRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  v : FinitePrimePlace 2 7
  completionEquiv :
    Completion (qVPlace (l := l) T b) ≃+* Completion (QPlace v)

/-- Layer (2): the actual integral units of the qVPlace algebraic closure are
identified with the canonical S2055 completion integral units at the same v. -/
structure S2040QVIntegralUnitsEquivRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T))
    (v : FinitePrimePlace 2 7) where
  unitsEquiv :
    (Integers (AlgebraicClosure (Completion (qVPlace (l := l) T b))))ˣ ≃*
      S2055CompletionIntegralUnits (QPlace v)

/-- Layer (3): the canonical S2046 norm/mu bridge at the chosen v. -/
abbrev S2040QVNormBridgeRequired
    (v : FinitePrimePlace 2 7) : Type :=
  S2046NormBridge v

/-- The three layers together are exactly the missing S2040 completion bridge. -/
noncomputable def S2040CompletionBridgeOfLayers
    {T : SourceNativeInitialThetaData.{0} l}
    {b : Bad (nativePlaceSelection T)}
    (R : S2040QVCompletionRingEquivRequired T b)
    (U : S2040QVIntegralUnitsEquivRequired T b R.v)
    (N : S2040QVNormBridgeRequired R.v) :
    S2040CompletionBridgeRequired T b :=
  { v := R.v
    qVCompletionEquiv := R.completionEquiv
    qVIntegralUnitsEquiv := U.unitsEquiv
    normBridge := N }

#check S2040QVCompletionRingEquivRequired
#check S2040QVIntegralUnitsEquivRequired
#check S2040QVNormBridgeRequired
#check S2040CompletionBridgeOfLayers

end LeanFormal.IUT.XiFPaper.S2040CompletionLayersActual
end
