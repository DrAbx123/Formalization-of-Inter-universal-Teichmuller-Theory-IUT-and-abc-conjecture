import tmp.sheaf.xif.paper.GlobalThetaPilotPlaceComparisonActualAdapted
import tmp.sheaf.xif.paper.PrimeStripLogShellActual

-- Actual D-/F-prime-strip and C3 place data for the global Theta-pilot map
--
-- Constructs the actual D-/F-prime-strip capsule and the actual C3 tensor
-- places/log-shells from PrimeStripLogShellActual. The missing bad-place ->
-- C3 tensor index map is recorded as an exact input/obstruction; no fake map.
-- WRITE-ONLY: no local lake/lean.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.GlobalThetaPilotPlaceMapActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotPossibleImageGeometryActual

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

-- Actual D-/F-prime-strip capsule from the source theater.
noncomputable def actualDFCapsule :
    ActualDFPrimeStripCapsule (I := I) :=
  actualDFPrimeStripCapsule (I := I)

-- Actual C3 place at each tensor index.
noncomputable def actualC3Place (i : C3.tensorIndex) :
    FinitePlaceAtPrime I.initial.arithmetic.Fmod C3.p :=
  c3LogShellPlace C3 i

-- Actual C3 log-shell at each tensor index.
noncomputable def actualC3LogShellAt (i : C3.tensorIndex) :
    Set (CommonPrimeCompletion (actualC3Place (I := I) C3 i)) :=
  actualC3LogShell C3 i

-- Exact missing map: the actual bad places of the native data to the actual
-- C3 tensor indices, respecting the theta values. This is a source input, not
-- a fabricated function.
structure BadToC3TensorMap where
  toIndex : Bad (nativePlaceSelection T) → C3.tensorIndex
  thetaValue_compat : Prop

def BadToC3TensorMapObstruction : Prop :=
  Nonempty (BadToC3TensorMap (I := I) C3 T)

-- Exact missing place comparison to the transport GlobalThetaPilotCarrier /
-- per-V ThetaPilotPoint strip places. The actual C3 place/log-shell side is
-- constructed above; the bad-place carrier map is explicit input data.
structure GlobalThetaPilotPlaceMapData where
  badToC3 : Bad (nativePlaceSelection T) → C3.tensorIndex
  c3Place : C3.tensorIndex → FinitePlaceAtPrime I.initial.arithmetic.Fmod C3.p
  carrierMap : Prop

def GlobalThetaPilotPlaceMapObstruction : Prop :=
  Nonempty (GlobalThetaPilotPlaceMapData (I := I) C3 T)

-- The actual C3 place/log-shell data are the PrimeStripLogShellActual data.
theorem actualC3Place_eq (i : C3.tensorIndex) :
    actualC3Place (I := I) C3 i = c3LogShellPlace C3 i := rfl

theorem actualC3LogShellAt_eq (i : C3.tensorIndex) :
    actualC3LogShellAt (I := I) C3 i = actualC3LogShell C3 i := rfl

#check actualDFCapsule
#check actualC3Place
#check actualC3LogShellAt
#check BadToC3TensorMap
#check BadToC3TensorMapObstruction
#check GlobalThetaPilotPlaceMapData
#check GlobalThetaPilotPlaceMapObstruction
#check actualC3Place_eq
#check actualC3LogShellAt_eq

end LeanFormal.IUT.XiFPaper.GlobalThetaPilotPlaceMapActualAdapted

end