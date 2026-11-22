import tmp.sheaf.xif.paper.C3TensorIndexBadEquivActualAdapted
import tmp.sheaf.xif.paper.ConcreteC3DonorAssemblyActual

-- Actual C3 tensor-index / Bad-place equivalence data
--
-- Actual base-place data from the concrete C3 donor assembly and the actual
-- bad native base places, plus the actual base-place compatibility relation
-- and fibers. An actual equivalence/index map is constructed only from an
-- explicit actual equivalence and compatibility proof; the missing source
-- comparison is an exact obstruction, not a fake map.
-- WRITE-ONLY: no local lake/lean.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.C3TensorIndexBadEquivDataActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.ConcreteC3DonorAssemblyActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (place : FinitePlaceAtPrime I.initial.arithmetic.Fmod 5)
variable (A : ConcreteC3DonorAssemblyActual (I := I) place)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

-- Actual base finite place of a concrete C3 tensor index.
noncomputable def c3TensorIndexPlace (i : A.tensorIndex) :
    FinitePlaceAtPrime I.initial.arithmetic.Fmod A.p :=
  A.tensorPlaces i (A.tensorTuple i)

-- Actual base finite place of a bad native place.
noncomputable def badPlaceAt (b : Bad (nativePlaceSelection T)) :
    NumberField.FinitePlace T.arithmetic.Fmod :=
  b.1

-- Actual base-place compatibility relation between a bad place and a C3 index.
def basePlaceCompatible (b : Bad (nativePlaceSelection T)) (i : A.tensorIndex) : Prop :=
  (c3TensorIndexPlace (I := I) place A i : NumberField.FinitePlace
    I.initial.arithmetic.Fmod) = badPlaceAt (I := I) T b

-- Actual fiber of C3 indices compatible with a bad place.
def basePlaceCompatibleFiber (b : Bad (nativePlaceSelection T)) :
    Set A.tensorIndex :=
  {i | basePlaceCompatible (I := I) place A T b i}

-- Actual equivalence data: index equivalence, base-place compatibility, and
-- theta-value compatibility.
structure C3TensorIndexBadEquivData where
  indexEquiv : A.tensorIndex ≃ Bad (nativePlaceSelection T)
  basePlace_compat : Prop
  thetaValue_compat : Prop

def C3TensorIndexBadEquivObstruction : Prop :=
  Nonempty (C3TensorIndexBadEquivData (I := I) place A T)

-- Conditional actual equivalence data from an explicit actual equivalence and
-- compatibility proof. No arbitrary equivalence is chosen.
noncomputable def c3TensorIndexBadEquivOfEquiv
    (e : A.tensorIndex ≃ Bad (nativePlaceSelection T))
    (hbase : Prop) (htheta : Prop) :
    C3TensorIndexBadEquivData (I := I) place A T where
  indexEquiv := e
  basePlace_compat := hbase
  thetaValue_compat := htheta

#check c3TensorIndexPlace
#check badPlaceAt
#check C3TensorIndexBadEquivData
#check C3TensorIndexBadEquivObstruction
#check c3TensorIndexBadEquivOfEquiv

end LeanFormal.IUT.XiFPaper.C3TensorIndexBadEquivDataActualAdapted

end