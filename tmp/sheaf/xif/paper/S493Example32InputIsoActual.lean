import tmp.sheaf.xif.paper.S462Example32PhiIsoGroupLikeActual
import tmp.sheaf.xif.paper.S474Example32GroupLikeIsoActual
import tmp.sheaf.xif.paper.S481AlignedDivisorMapActual
import tmp.sheaf.xif.paper.S468DivisorNaturalityActual
import Iut.Foundations.SourceModelFrobenioidPresentation
/-! # S493: Example32 Input with IsFSM := IsIso
Combine S462 example32PhiIso, S474 example32RationalFunctionsIso, and the
S481 aligned divisor.  The S481 divisor targets example32PhiIsFSM (IsFSM =
Example32IsFSM); its obj/gpPullback are the same constant-identity bodies as
example32PhiIso, and this is recorded by rfl lemmas. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S493Example32InputIsoActual
open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open LeanFormal.IUT.XiFPaper.S462Example32PhiIsoGroupLikeActual
open LeanFormal.IUT.XiFPaper.S474Example32GroupLikeIsoActual
open LeanFormal.IUT.XiFPaper.S481AlignedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S480Example32InputActual
open LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual
open Iut.SourceModelFrobenioid
universe u
variable (K : Type u) [Field K]
/-- S462 phi with IsFSM = IsIso. -/
abbrev PhiIso : DivisorialMonoidOn (Example32SmallBase K)
    (S462Example32PhiIsoGroupLikeActual.Example32FSMIso (K := K)) :=
  S462Example32PhiIsoGroupLikeActual.example32PhiIso (K := K)
/-- S480 phi with IsFSM = Example32IsFSM. -/
abbrev PhiFSM : DivisorialMonoidOn (Example32SmallBase K)
    (Example32IsFSM (K := K)) :=
  example32PhiIsFSM (K := K)
/-- S474 rational functions with IsFSM = IsIso. -/
abbrev RFIso : GroupLikeAddMonoidOn (Example32SmallBase K)
    (S474Example32GroupLikeIsoActual.Example32FSMIso (K := K)) :=
  S474Example32GroupLikeIsoActual.example32RationalFunctionsIso (K := K)
theorem phi_obj_eq (X : Example32SmallBase K) :
    (PhiIso K).obj X = (PhiFSM K).obj X := rfl
theorem phi_gpPullback_eq {X Y : Example32SmallBase K} (f : X ⟶ Y) :
    (PhiIso K).gpPullback f = (PhiFSM K).gpPullback f := rfl
/-- S481 aligned divisor re-targeted to PhiIso. -/
noncomputable def alignedDivisorIso
    (Vf : DvSmallValuationFamily (K := K)) (X : Example32SmallBase K) :
    (RFIso K).obj X →+
      Algebra.GrothendieckAddGroup ((PhiIso K).obj X).carrier := by
  letI : Field (coverField (K := K) X) := coverFieldField X
  letI : Algebra K (coverField (K := K) X) := inferInstance
  exact example32AlignedDivisor (K := K) Vf X
/-- Conditional data for the IsFSM=IsIso Input. -/
structure Example32InputDataIso where
  valuationFamily : DvSmallValuationFamily (K := K)
  divisor_naturality :
    ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y)
      (value : (RFIso K).obj Y),
      alignedDivisorIso K valuationFamily X
          ((RFIso K).pullback f value) =
        (PhiIso K).gpPullback f
          (alignedDivisorIso K valuationFamily Y value)
/-- Actual Input with IsFSM = IsIso, S474 rational functions, aligned divisor. -/
noncomputable def example32InputIso
    (D : Example32InputDataIso K) : Input (PhiIso K) where
  rationalFunctions := RFIso K
  divisor X := alignedDivisorIso K D.valuationFamily X
  divisor_natural := D.divisor_naturality
/-- Conditional FrobenioidPresentation with IsFSM = IsIso. -/
noncomputable def example32FrobenioidPresentationIso
    (D : Example32InputDataIso K)
    [IsConnected (Example32SmallBase K)]
    (baseTotallyEpimorphic :
      ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y), Epi f) :
    FrobenioidPresentation :=
  SourceModelFrobenioid.Carrier.frobenioidPresentation
    (Phi := PhiIso K) (data := example32InputIso K D)
    baseTotallyEpimorphic
end LeanFormal.IUT.XiFPaper.S493Example32InputIsoActual
