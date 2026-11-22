import tmp.sheaf.xif.paper.OtriangleLogVolumeObjectActual
import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual

-- S862: actual O-triangle log-volume interface with paper q/root orders.
-- Uses S170 O-triangle object, S63O/S150 normalization, S782 divisor orders.
-- NonunitHaarRequired / RootThetaNormalizationRequired are exact fields;
-- no completion/field Haar is used as O-triangle Haar.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S862OtriLogVolumeInterfacePaperActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.OtriangleLogVolumeObjectActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The actual paper completion place as a `FinitePlaceAtPrime`. -/
noncomputable def paperOtriPlace : FinitePlaceAtPrime T.arithmetic.F (qVFamTensorP T b) :=
  qVFamTensorPlaces T b () ()

/-- Paper q/root divisor orders from S782. -/
noncomputable def otriQDivisorOrder : Real :=
  (stackDivisorSection (l := l) T b (stackQSection (l := l) T b)).toAdd
noncomputable def otriRootDivisorOrder : Real :=
  (stackDivisorSection (l := l) T b (stackRootSection (l := l) T b)).toAdd

theorem otriRootDivisorOrder_eq :
    otriRootDivisorOrder (l := l) T b =
      ((qVFamily T b).order : Real) / (2 * (l.value : Real)) :=
  rfl

theorem otriQDivisorOrder_eq :
    otriQDivisorOrder (l := l) T b = ((qVFamily T b).order : Real) :=
  rfl

/-- Paper q-pilot log at the O-triangle: -order log p. -/
noncomputable def otriQLogVolume : Real :=
  -(((qVFamily T b).order : Real) *
    Real.log (qVFamTensorP T b : Real))

/-- Paper root log at the O-triangle: -(order/(2l)) log p. -/
noncomputable def otriRootLogVolume : Real :=
  -((((qVFamily T b).order : Real) / (2 * (l.value : Real))) *
    Real.log (qVFamTensorP T b : Real))

/-- Least lambda-O hull log: -sum cRoot log p. -/
noncomputable def otriLeastHullLog : Real :=
  -((∑ _ : qVFamTensorV, paperRootCoefficientFamily T b ()) *
    Real.log (qVFamTensorP T b : Real))

theorem otriLeastHullLog_eq_formula :
    otriLeastHullLog (l := l) T b =
      -((∑ _ : qVFamTensorV, paperRootCoefficientFamily T b ()) *
        Real.log (qVFamTensorP T b : Real)) := rfl

/-- Actual O-triangle log-volume interface with exact gaps. -/
structure OtriLogVolumeInterfacePaper where
  otri : OtriangleLogVolumeObject (K := T.arithmetic.F) (p := qVFamTensorP T b)
    (paperOtriPlace T b)
  qDivisorOrder : Real
  qDivisorOrder_eq : qDivisorOrder = otriQDivisorOrder (l := l) T b
  rootDivisorOrder : Real
  rootDivisorOrder_eq : rootDivisorOrder = otriRootDivisorOrder (l := l) T b
  logVolume_q : Real
  logVolume_q_eq : logVolume_q = otriQLogVolume (l := l) T b
  logVolume_root : Real
  logVolume_root_eq : logVolume_root = otriRootLogVolume (l := l) T b
  leastHullLog : Real
  leastHullLog_eq : leastHullLog = otriLeastHullLog (l := l) T b
  nonunitHaar : Prop
  nonunitHaar_eq : nonunitHaar =
    NonunitHaarRequired (K := T.arithmetic.F) (p := qVFamTensorP T b)
      (paperOtriPlace T b)
  rootThetaNormalization : Prop
  rootThetaNormalization_eq : rootThetaNormalization =
    RootThetaNormalizationRequired (K := T.arithmetic.F)
      (p := qVFamTensorP T b) (paperOtriPlace T b)

noncomputable def otriLogVolumeInterfacePaper :
    OtriLogVolumeInterfacePaper (l := l) T b where
  otri := otriangleLogVolumeObject (K := T.arithmetic.F)
    (p := qVFamTensorP T b) (paperOtriPlace T b)
  qDivisorOrder := otriQDivisorOrder (l := l) T b
  qDivisorOrder_eq := rfl
  rootDivisorOrder := otriRootDivisorOrder (l := l) T b
  rootDivisorOrder_eq := rfl
  logVolume_q := otriQLogVolume (l := l) T b
  logVolume_q_eq := rfl
  logVolume_root := otriRootLogVolume (l := l) T b
  logVolume_root_eq := rfl
  leastHullLog := otriLeastHullLog (l := l) T b
  leastHullLog_eq := rfl
  nonunitHaar := NonunitHaarRequired (K := T.arithmetic.F)
    (p := qVFamTensorP T b) (paperOtriPlace T b)
  nonunitHaar_eq := rfl
  rootThetaNormalization := RootThetaNormalizationRequired (K := T.arithmetic.F)
    (p := qVFamTensorP T b) (paperOtriPlace T b)
  rootThetaNormalization_eq := rfl

/-- Exact remaining O-triangle inputs. -/
def OtriNonunitHaarAndRootThetaRequired : Prop :=
  NonunitHaarRequired (K := T.arithmetic.F) (p := qVFamTensorP T b)
    (paperOtriPlace T b) ∧
  RootThetaNormalizationRequired (K := T.arithmetic.F)
    (p := qVFamTensorP T b) (paperOtriPlace T b)

#check otriLogVolumeInterfacePaper
#check OtriNonunitHaarAndRootThetaRequired

end LeanFormal.IUT.XiFPaper.S862OtriLogVolumeInterfacePaperActual

end