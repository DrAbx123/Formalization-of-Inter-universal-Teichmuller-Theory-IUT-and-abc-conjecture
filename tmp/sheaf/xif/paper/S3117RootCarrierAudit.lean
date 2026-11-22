import tmp.sheaf.n8.closure.SourcePilotRegion
import tmp.sheaf.n8.closure.C3Roots
import LeanFormal.IUT.IUTII.Kummer.NatRootSystem
import LeanFormal.IUT.IUTII.Kummer.KummerClass
import tmp.sheaf.n8.closure.NativeC3
import tmp.sheaf.n8.closure.NativeInput
import tmp.sheaf.xif.paper.S3115NativeSourcePilotRegionDonors

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.S3115NativeSourcePilotRegionDonors
open LeanFormal.IUT.NumberFieldFinitePlace
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 160000

namespace LeanFormal.IUT.XiFPaper.S3117RootCarrierAudit

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput l V}
variable (p : Nat) [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
variable (q : FinitePlaceQCandidate place.val)

/-- The corrected root carrier: roots live in the algebraic closure of the
base completion, not in the completion itself. -/
structure S3117CorrectedRoots where
  qUnit : (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ
  roots : NatRootSystem (unitToAlgClosed qUnit)
  roots' : NatRootSystem (unitToAlgClosed qUnit)
  kummerClass : CyclotomicTower
    (AlgebraicClosure (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place))
  rootChange : CyclotomicTower
    (AlgebraicClosure (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place))
  rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'

/-- Actual inhabitant: alg-closed roots always exist for a q-candidate. -/
noncomputable def S3117CorrectedRootsOfQ : S3117CorrectedRoots (I := I) p place where
  qUnit := Units.mk0 q.q q.q_ne_zero
  roots := algClosedRootSystem (Units.mk0 q.q q.q_ne_zero)
  roots' := algClosedRootSystem (Units.mk0 q.q q.q_ne_zero)
  kummerClass := KummerClass.rootSystemDiff
    (algClosedRootSystem (Units.mk0 q.q q.q_ne_zero))
    (algClosedRootSystem (Units.mk0 q.q q.q_ne_zero))
  rootChange := KummerClass.rootSystemDiff
    (algClosedRootSystem (Units.mk0 q.q q.q_ne_zero))
    (algClosedRootSystem (Units.mk0 q.q q.q_ne_zero))
  rootChange_eq := rfl


variable (X : N8NativeInput fiveLabel)
variable [Fintype (Bad (nativePlaceSelection X.S))]

/-- Corrected native root carrier: algebraic-closure units, aligned with
nativeRootsActual. -/
structure S3117NativeAlgRoots where
  qUnit : (Completion (nativeFPlaceOverBad X))ˣ
  roots : NatRootSystem (unitToAlgClosed qUnit)
  roots' : NatRootSystem (unitToAlgClosed qUnit)
  kummerClass : CyclotomicTower
    (AlgebraicClosure (Completion (nativeFPlaceOverBad X)))
  rootChange : CyclotomicTower
    (AlgebraicClosure (Completion (nativeFPlaceOverBad X)))
  rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'

/-- Actual inhabitant from native root/Kummer data. -/
noncomputable def S3117NativeAlgRootsActual : S3117NativeAlgRoots X where
  qUnit := nativeQUnitActual X
  roots := nativeRootsActual X
  roots' := nativeRootsActual X
  kummerClass := nativeKummerClassActual X
  rootChange := nativeKummerClassActual X
  rootChange_eq := rfl


/-- Corrected BK carrier: roots/Kummer live in the algebraic closure. -/
structure S3117BK (X : N8NativeInput fiveLabel)
    [Fintype (Bad (nativePlaceSelection X.S))] where
  qUnit : (Completion (nativeFPlaceOverBad X))ˣ
  roots : NatRootSystem (unitToAlgClosed qUnit)
  roots' : NatRootSystem (unitToAlgClosed qUnit)
  kummerClass : CyclotomicTower
    (AlgebraicClosure (Completion (nativeFPlaceOverBad X)))
  rootChange : CyclotomicTower
    (AlgebraicClosure (Completion (nativeFPlaceOverBad X)))
  rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'

/-- Actual BK from native root/Kummer data (no descent). -/
noncomputable def S3117BKActual (X : N8NativeInput fiveLabel)
    [Fintype (Bad (nativePlaceSelection X.S))] : S3117BK X where
  qUnit := nativeQUnitActual X
  roots := nativeRootsActual X
  roots' := nativeRootsActual X
  kummerClass := nativeKummerClassActual X
  rootChange := nativeKummerClassActual X
  rootChange_eq := rfl

/-- Explicit bridge target if a downstream needs the completion carrier. -/
def S3117CompletionBridgeTarget (X : N8NativeInput fiveLabel)
    [Fintype (Bad (nativePlaceSelection X.S))] : Prop :=
  Nonempty (S3115BK X)


/-- Exact bridge target to the completion-carrier BK. -/
def S3117BridgeToCompletionBKTtarget : Prop :=
  Nonempty (S3115BK X)

#check S3117BK
#check S3117BKActual
#check S3117CompletionBridgeTarget
#check S3117NativeAlgRoots
#check S3117NativeAlgRootsActual
#check S3117BridgeToCompletionBKTtarget


#check S3117CorrectedRoots
#check S3117CorrectedRootsOfQ

end LeanFormal.IUT.XiFPaper.S3117RootCarrierAudit
end