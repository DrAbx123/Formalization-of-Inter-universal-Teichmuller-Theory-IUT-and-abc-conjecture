import tmp.sheaf.xif.paper.GlobalThetaPilotPlaceMapActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import tmp.sheaf.n8.closure.NativeSourceReductionActual

-- Actual bad-place to C3 tensor-index map: construction/obstruction
--
-- The C3 side is actual: each tensor index has its actual base finite place
-- C3.tensorPlaces i (C3.tensorTuple i). The bad side is actual: each bad place
-- has its actual base place b.1. An actual index map must preserve these base
-- places and the theta-value data. No such source place comparison exists in
-- the tree, so the map is recorded as an exact conditional input/obstruction,
-- not fabricated. WRITE-ONLY: no local lake/lean.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.BadToC3TensorMapActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace

universe ua uv upi umon ui v w

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

-- Actual base finite place of a C3 tensor index.
noncomputable def c3TensorBasePlace (i : C3.tensorIndex) :
    FinitePlaceAtPrime I.initial.arithmetic.Fmod C3.p :=
  C3.tensorPlaces i (C3.tensorTuple i)

-- Actual base finite place of a bad native place.
noncomputable def badBasePlace (b : Bad (nativePlaceSelection T)) :
    NumberField.FinitePlace T.arithmetic.Fmod :=
  b.1

-- Exact data of a bad-place to C3 tensor-index map: actual index map, actual
-- base-place compatibility, and theta-value compatibility.
structure BadToC3TensorMapData where
  toIndex : Bad (nativePlaceSelection T) → C3.tensorIndex
  basePlace_compat : Prop
  thetaValue_compat : Prop

def BadToC3TensorMapObstruction : Prop :=
  Nonempty (BadToC3TensorMapData (I := I) C3 T)

-- Conditional actual map from an explicit index equivalence with base-place
-- compatibility. The equivalence is actual data, not a choice.
noncomputable def badToC3TensorMapOfEquiv
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (hplace : Prop) (htheta : Prop) :
    BadToC3TensorMapData (I := I) C3 T where
  toIndex := e
  basePlace_compat := hplace
  thetaValue_compat := htheta

#check c3TensorBasePlace
#check badBasePlace
#check BadToC3TensorMapData
#check BadToC3TensorMapObstruction
#check badToC3TensorMapOfEquiv

end LeanFormal.IUT.XiFPaper.BadToC3TensorMapActual

end