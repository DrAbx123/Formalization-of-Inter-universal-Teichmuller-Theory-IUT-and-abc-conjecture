import tmp.sheaf.xif.paper.S227TensorHullHaarActual
import tmp.sheaf.xif.paper.RootTensorHaarTransportActual
import tmp.sheaf.xif.paper.PaperFinalLValuedHaarMuLogGapActual

/-! # S238: product tensor hull Haar/log and qside block normalization -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S238ProductTensorHullHaarActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual
open LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual
open LeanFormal.IUT.XiFPaper.S214RootThetaNormTensorActual
open LeanFormal.IUT.XiFPaper.S227TensorHullHaarActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedHaarMuLogGapActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

noncomputable def productBlockHaar :
    Measure ((b : Bad (nativePlaceSelection T)) → rootTensorBlock T b) :=
  Measure.pi (fun b => blockHaar T b)

noncomputable def productRootNormedHaar :
    Measure ((b : Bad (nativePlaceSelection T)) → rootNormedExtension T b) :=
  Measure.pi (fun b => rootNormedHaar T b)

noncomputable def productTensorHull :
    Set ((b : Bad (nativePlaceSelection T)) → rootTensorBlock T b) :=
  Set.pi (Set.univ : Set (Bad (nativePlaceSelection T)))
    (fun b => tensorLambdaOHull (T := T) b)

noncomputable def productLHull :
    Set ((b : Bad (nativePlaceSelection T)) → rootNormedExtension T b) :=
  Set.pi (Set.univ : Set (Bad (nativePlaceSelection T)))
    (fun b => LFieldUnitHull (T := T) b)

noncomputable def tensorNormalizationFactor (b : Bad (nativePlaceSelection T)) : Real :=
  (blockHaar T b (blockUnitBall T b)).toReal /
    (tensorHaarTransport (T := T) b (blockUnitBall T b)).toReal

structure ProductTensorHullHaarLogObject where
  blockHaar : Measure ((b : Bad (nativePlaceSelection T)) → rootTensorBlock T b)
  blockHaar_eq : blockHaar = productBlockHaar (T := T)
  rootNormedHaar : Measure ((b : Bad (nativePlaceSelection T)) → rootNormedExtension T b)
  rootNormedHaar_eq : rootNormedHaar = productRootNormedHaar (T := T)
  tensorHull : Set ((b : Bad (nativePlaceSelection T)) → rootTensorBlock T b)
  tensorHull_eq : tensorHull = productTensorHull (T := T)
  LHull : Set ((b : Bad (nativePlaceSelection T)) → rootNormedExtension T b)
  LHull_eq : LHull = productLHull (T := T)
  factor : Bad (nativePlaceSelection T) → Real
  factor_eq : factor = tensorNormalizationFactor (T := T)
  tensorHullLog : Real
  LHullLog : Real

noncomputable def productTensorHullHaarLogObject :
    ProductTensorHullHaarLogObject (T := T) where
  blockHaar := productBlockHaar (T := T)
  blockHaar_eq := rfl
  rootNormedHaar := productRootNormedHaar (T := T)
  rootNormedHaar_eq := rfl
  tensorHull := productTensorHull (T := T)
  tensorHull_eq := rfl
  LHull := productLHull (T := T)
  LHull_eq := rfl
  factor := tensorNormalizationFactor (T := T)
  factor_eq := rfl
  tensorHullLog := Real.log
    ((productBlockHaar (T := T)) (productTensorHull (T := T))).toReal
  LHullLog := Real.log
    ((productRootNormedHaar (T := T)) (productLHull (T := T))).toReal

end LeanFormal.IUT.XiFPaper.S238ProductTensorHullHaarActual

end
