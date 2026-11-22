import tmp.sheaf.xif.paper.S369OtriSplitFrobenioidActual

/-! # S373: exact CharacteristicSplitting statement for the native stage model

S369 constructs the actual stage FrobenioidPresentation and rational monoid
transport.  Repo search shows no CharacteristicSplitting instance for it.
This file gives the weakest explicit statement (a tau-family with the five
Definition 2.3 laws), proves it equivalent to Nonempty CharacteristicSplitting,
and constructs a CharacteristicSplitting only conditionally from the tau data.

No fake split; no completion/L; no inequality.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S373NativeStageSplittingActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S369OtriSplitFrobenioidActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual stage presentation. -/
abbrev stagePresentation : Iut.FrobenioidPresentation :=
  nativeStageFrobenioidPresentation T b

/-- The actual stage rational monoid transport. -/
abbrev stageTransport :
    (stagePresentation T b).preFrobenioid.RationalMonoidTransport :=
  nativeStageRationalMonoidTransport T b

/-- Weakest explicit tau data for a CharacteristicSplitting of the stage
transport: a tau submonoid plus the five Definition 2.3 laws. -/
structure StageCharacteristicTauData where
  tau : ∀ X : (stagePresentation T b).preFrobenioid.IsotropicLinearObject,
    Submonoid ((stagePresentation T b).preFrobenioid.LinearBaseIdentityEndomorphism
      X.obj)
  pullback_mem :
    ∀ {X Y : (stagePresentation T b).preFrobenioid.IsotropicLinearObject}
      (f : X ⟶ Y)
      (value : (stagePresentation T b).preFrobenioid.LinearBaseIdentityEndomorphism
        Y.obj),
      value ∈ tau Y →
        (stageTransport T b).pullback f value ∈ tau X
  units_commute :
    ∀ (X : (stagePresentation T b).preFrobenioid.IsotropicLinearObject)
      (unit : Units ((stagePresentation T b).preFrobenioid.LinearBaseIdentityEndomorphism
        X.obj))
      (characteristic : tau X),
      Commute
        (unit : (stagePresentation T b).preFrobenioid.LinearBaseIdentityEndomorphism
          X.obj)
        characteristic.1
  multiplication_bijective :
    ∀ X : (stagePresentation T b).preFrobenioid.IsotropicLinearObject,
      Function.Bijective
        (fun pair :
            Units ((stagePresentation T b).preFrobenioid.LinearBaseIdentityEndomorphism
              X.obj) × tau X =>
          (pair.1 :
              (stagePresentation T b).preFrobenioid.LinearBaseIdentityEndomorphism
                X.obj) *
            pair.2.1)
  isotropicHull_mem_range :
    ∀ (A : (stagePresentation T b).carrier)
      (hull : (stagePresentation T b).preFrobenioid.IsotropicHull A)
      (characteristic :
        tau
          { obj := hull.hull
            isotropic := hull.isotropic }),
      characteristic.1 ∈ Set.range
        ((stageTransport T b).hullInclusion A hull)

/-- Exact weakest statement: a stage tau-family satisfying the five laws. -/
def NativeStageCharacteristicSplittingExact : Prop :=
  Nonempty (StageCharacteristicTauData (T := T) (b := b))

/-- Construct the actual CharacteristicSplitting from explicit tau data. -/
noncomputable def characteristicSplittingOfTauData
    (D : StageCharacteristicTauData (T := T) (b := b)) :
    (stagePresentation T b).preFrobenioid.CharacteristicSplitting
      (stageTransport T b) where
  tau := D.tau
  pullback_mem := D.pullback_mem
  units_commute := D.units_commute
  multiplication_bijective := D.multiplication_bijective
  isotropicHull_mem_range := D.isotropicHull_mem_range

/-- The exact tau statement is equivalent to the repo's
CharacteristicSplitting structure. -/
theorem nativeStageCharacteristicSplittingExact_iff :
    NativeStageCharacteristicSplittingExact (T := T) (b := b) ↔
      Nonempty ((stagePresentation T b).preFrobenioid.CharacteristicSplitting
        (stageTransport T b)) := by
  constructor
  · rintro ⟨D⟩
    exact ⟨characteristicSplittingOfTauData T b D⟩
  · rintro ⟨C⟩
    exact ⟨{ tau := C.tau
             pullback_mem := C.pullback_mem
             units_commute := C.units_commute
             multiplication_bijective := C.multiplication_bijective
             isotropicHull_mem_range := C.isotropicHull_mem_range }⟩

/-- The existing S369 gap is exactly this tau statement. -/
theorem nativeStageCharacteristicSplittingGap_iff :
    NativeStageCharacteristicSplittingGap (T := T) (b := b) ↔
      NativeStageCharacteristicSplittingExact (T := T) (b := b) := by
  unfold NativeStageCharacteristicSplittingGap
    NativeStageCharacteristicSplittingExact
  exact (nativeStageCharacteristicSplittingExact_iff T b).symm

end LeanFormal.IUT.XiFPaper.S373NativeStageSplittingActual

end
