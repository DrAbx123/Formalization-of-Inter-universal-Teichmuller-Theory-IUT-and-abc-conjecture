import tmp.sheaf.xif.paper.S3136ModelSourceClauseActual
import tmp.sheaf.xif.paper.S3136ModelClauseWitnessAdapterActual
import tmp.sheaf.xif.paper.S3136NativeHaarFamilyActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual

/-! # Stage-4 host: native theta datum together with its concrete Haar family

Source anchors: IUT I, Definition 3.1; IUT III, Prop. 3.2, (ii) (tensor packets
with additive Haar); IUT III, Remark 3.9.4.

CONSUMER: hull's S3132ConcreteSourceVFormInstantiatedActual consumes
(T, mu := lgpNativeHaarFamily T).  This file bundles the pair so consumers get
the native datum and its concrete additive Haar family in one term:
* lgpModelNativeDataWithHaar: from the exact missing clause data
  (LGPModelSourceClauseMissing) -> (native datum, family of additive Haar
  measures on its qVFamTensorBlock comptetions), with the arithmetic theorem;
* lgpConcreteClauseNativeDataWithHaar: the same for LGPConcreteClauseData.

LABEL: prerequisite component.  Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136ModelNativeDataWithHaarActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
open LeanFormal.IUT.XiFPaper.S3136ModelClauseWitnessAdapterActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open MeasureTheory

variable {l : PrimeGeFive}

/-- A native initial-Theta datum together with its concrete additive Haar family
on the native one-factor tensor block. -/
structure LGPModelNativeDataWithHaar (l : PrimeGeFive) where
  datum : SourceNativeInitialThetaData.{0} l
  haar : (b : Bad (nativePlaceSelection datum)) →
    Measure (qVFamTensorBlock datum b)
  haar_isAddHaar :
    (b : Bad (nativePlaceSelection datum)) →
      Measure.IsAddHaarMeasure (haar b)

/-- From the exact missing clause data: the native datum together with the
concrete additive Haar family. -/
def lgpModelNativeDataWithHaar
    (M : LGPModelSourceClauseMissing l) :
    LGPModelNativeDataWithHaar l :=
  let T := lgpModelNativeData M
  { datum := T
    haar := lgpNativeHaarFamily T
    haar_isAddHaar := lgpNativeHaarFamily_isAddHaar T }

/-- The bundled datum has the concrete Gaussian arithmetic. -/
theorem lgpModelNativeDataWithHaar_arithmetic
    (M : LGPModelSourceClauseMissing l) :
    (lgpModelNativeDataWithHaar M).datum.arithmetic =
      concreteGaussianInitialThetaArithmeticData l := by
  unfold lgpModelNativeDataWithHaar lgpModelNativeData
  exact lgpModelNativeData_arithmetic M

/-- The same bundle from concrete clause data. -/
def lgpConcreteClauseNativeDataWithHaar
    (M : LGPConcreteClauseData l) :
    LGPModelNativeDataWithHaar l :=
  let T := lgpConcreteClauseData_toNativeData M
  { datum := T
    haar := lgpNativeHaarFamily T
    haar_isAddHaar := lgpNativeHaarFamily_isAddHaar T }

#check LGPModelNativeDataWithHaar
#check lgpModelNativeDataWithHaar
#check lgpModelNativeDataWithHaar_arithmetic
#check lgpConcreteClauseNativeDataWithHaar

end LeanFormal.IUT.XiFPaper.S3136ModelNativeDataWithHaarActual
end