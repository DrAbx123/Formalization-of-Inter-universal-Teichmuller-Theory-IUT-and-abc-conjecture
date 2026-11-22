import tmp.sheaf.n8.closure.C3Actual
import tmp.sheaf.n8.closure.NativeC3
import tmp.sheaf.xif.paper.C3DonorFieldsFromSource
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.NumberFieldFinitePlace
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3114DonorFromTAttempt

variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable (I : OriginalInput fiveLabel (FinitePrimePlace 2 7))

/-- A chosen bad base Fmod place from the source bad-moduli set. -/
noncomputable def S3114BasePlace : NumberField.FinitePlace T.arithmetic.Fmod :=
  T.tuple.source.V_mod_bad_nonempty.choose

theorem S3114BasePlace_mem :
    S3114BasePlace T ∈ T.tuple.source.V_mod_bad :=
  T.tuple.source.V_mod_bad_nonempty.choose_spec

variable (hT : T.arithmetic = S1280Arithmetic fiveLabel)

/-- Type equality between the Fmod and F finite-place types under concrete
Gaussian arithmetic. -/
def S3114PlaceTypeEq :
    NumberField.FinitePlace T.arithmetic.Fmod =
      NumberField.FinitePlace T.arithmetic.F :=
  (congrArg (fun A : InitialThetaArithmeticData fiveLabel =>
      NumberField.FinitePlace A.Fmod) hT).trans
    ((by rfl : NumberField.FinitePlace (S1280Arithmetic fiveLabel).Fmod =
        NumberField.FinitePlace (S1280Arithmetic fiveLabel).F).trans
      (congrArg (fun A : InitialThetaArithmeticData fiveLabel =>
        NumberField.FinitePlace A.F) hT).symm)

/-- The chosen base place as an F-place, along the type equality. -/
noncomputable def S3114FPlace : NumberField.FinitePlace T.arithmetic.F :=
  S3114PlaceTypeEq T hT ▸ S3114BasePlace T


/-- Exact membership target for the F-place: the comap back to Fmod must be the
chosen base place. -/
def S3114FPlaceMemTarget : Prop :=
  NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) (S3114FPlace T hT) ∈
    T.tuple.source.V_mod_bad

/-- Exact donor target. -/
def S3114ConcreteDonorTarget : Prop :=
  Nonempty (SourcePilotRegionDonors (l := fiveLabel) (V := FinitePrimePlace 2 7) I)

#check S3114BasePlace
#check S3114BasePlace_mem
#check S3114PlaceTypeEq
#check S3114FPlace
#check S3114FPlaceMemTarget
#check S3114ConcreteDonorTarget

end LeanFormal.IUT.XiFPaper.S3114DonorFromTAttempt
end