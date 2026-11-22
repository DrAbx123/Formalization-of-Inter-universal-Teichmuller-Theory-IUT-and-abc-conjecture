import tmp.sheaf.xif.paper.S2040CompletionLayersActual
import tmp.sheaf.xif.paper.S2056IsometricClosureActual

/-! # S2040 norm bridge from the S2056 closure isometry

Layer (3) of the completion bridge is constructed from the S2056 isometric
algebraic-closure equivalence, using the canonical S2055/S2046 carriers.
Layers (1) and (2) remain exact missing at qVPlace: the qVPlace completion is a
finite extension of Q_p and source split/descent data are needed for a ring
isomorphism to a rational QPlace completion. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2040NormBridgeS2056Actual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.S2055CompletionIntegralUnitsActual
open LeanFormal.IUT.XiFPaper.S2046CompletionOUnitsActual
open LeanFormal.IUT.XiFPaper.S2056IsometricClosureActual
open LeanFormal.IUT.XiFPaper.S2040CompletionLayersActual
open LeanFormal.IUT.XiFPaper.S2040CompletionBridgeS2055Actual
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

universe u

/-- Layer (3): S2056's isometric closure equivalence constructs the canonical
S2046 norm/mu bridge at v. -/
noncomputable def s2040NormBridgeOfS2056Isometry
    (v : FinitePrimePlace 2 7)
    (I : S2056ClosureIsometry (QPlace v)) :
    S2046NormBridge v where
  identification := S2056IntegralUnitsEquiv (QPlace v) I
  muCompatible :=
    TimesMuQuotient.congr (S2056IntegralUnitsEquiv (QPlace v) I)

/-- Exact missing layer (1): qVPlace completion split/descent data giving a
ring isomorphism to a rational QPlace completion, in particular residue degree
and ramification index one at the chosen place. -/
structure S2040QVPlaceSplitData
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  v : FinitePrimePlace 2 7
  completionEquiv :
    Completion (qVPlace (l := l) T b) ≃+* Completion (QPlace v)
  completion_isometry :
    ∀ x : Completion (qVPlace (l := l) T b),
      ‖completionEquiv x‖ = ‖x‖

/-- Exact missing layer (2): the integral units of the qVPlace algebraic closure
identified with the canonical S2055 carrier at the same rational v. -/
structure S2040QVIntegralUnitsBridgeRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T))
    (v : FinitePrimePlace 2 7) where
  integralUnitsEquiv :
    (Integers (AlgebraicClosure (Completion (qVPlace (l := l) T b))))ˣ ≃*
      S2055CompletionIntegralUnits (QPlace v)

/-- With split data (1) and integral-units bridge (2), plus S2056's isometry,
the full completion bridge is assembled. -/
noncomputable def s2040CompletionBridgeOfSplitAndS2056
    {T : SourceNativeInitialThetaData.{0} l}
    {b : Bad (nativePlaceSelection T)}
    (S : S2040QVPlaceSplitData T b)
    (U : S2040QVIntegralUnitsBridgeRequired T b S.v)
    (I : S2056ClosureIsometry (QPlace S.v)) :
    S2040CompletionBridgeRequired T b :=
  S2040CompletionBridgeOfLayers
    { v := S.v, completionEquiv := S.completionEquiv }
    { unitsEquiv := U.integralUnitsEquiv }
    (s2040NormBridgeOfS2056Isometry S.v I)

#check s2040NormBridgeOfS2056Isometry
#check S2040QVPlaceSplitData
#check S2040QVIntegralUnitsBridgeRequired
#check s2040CompletionBridgeOfSplitAndS2056

end LeanFormal.IUT.XiFPaper.S2040NormBridgeS2056Actual
end
