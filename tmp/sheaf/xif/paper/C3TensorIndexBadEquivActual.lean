import tmp.sheaf.xif.paper.BadToC3TensorMapActual
import tmp.sheaf.n8.closure.C3Actual

-- Actual C3 tensor index / Bad place equivalence data: construction/obstruction
--
-- The concrete C3 donor supplies an actual tensorIndex type with Fintype and
-- actual tensor places D.tensorPlaces i (D.tensorTuple i). The bad native
-- side supplies Bad (nativePlaceSelection T). The donor does not provide an
-- actual index equivalence or base-place compatibility; these are recorded as
-- exact conditional data/obstruction, not fabricated. WRITE-ONLY.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.C3TensorIndexBadEquivActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (D : SourcePilotRegionDonors (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

-- Actual base finite place of a concrete C3 donor tensor index.
noncomputable def c3TensorIndexBasePlace (i : D.tensorIndex) :
    FinitePlaceAtPrime I.initial.arithmetic.Fmod D.p :=
  D.tensorPlaces i (D.tensorTuple i)

-- Actual base finite place of a bad native place.
noncomputable def badIndexBasePlace (b : Bad (nativePlaceSelection T)) :
    NumberField.FinitePlace T.arithmetic.Fmod :=
  b.1

-- Exact data of an actual C3 tensor index / Bad-place equivalence with
-- base-place and theta-value compatibility.
structure C3TensorIndexBadEquivData where
  indexEquiv : D.tensorIndex ≃ Bad (nativePlaceSelection T)
  basePlace_compat : Prop
  thetaValue_compat : Prop

def C3TensorIndexBadEquivObstruction : Prop :=
  Nonempty (C3TensorIndexBadEquivData (I := I) D T)

-- Conditional actual equivalence data from an explicit index equivalence and
-- exact compatibility hypotheses. No arbitrary equivalence is chosen.
noncomputable def c3TensorIndexBadEquivOfData
    (e : D.tensorIndex ≃ Bad (nativePlaceSelection T))
    (hbase : Prop) (htheta : Prop) :
    C3TensorIndexBadEquivData (I := I) D T where
  indexEquiv := e
  basePlace_compat := hbase
  thetaValue_compat := htheta

#check c3TensorIndexBasePlace
#check badIndexBasePlace
#check C3TensorIndexBadEquivData
#check C3TensorIndexBadEquivObstruction
#check c3TensorIndexBadEquivOfData

end LeanFormal.IUT.XiFPaper.C3TensorIndexBadEquivActual

end