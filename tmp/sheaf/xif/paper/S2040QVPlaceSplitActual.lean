import tmp.sheaf.xif.paper.S2040NormBridgeS2056Actual
import tmp.sheaf.xif.paper.BadPlaceRationalDegreeActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.QVFamTensorBlockAlignmentActual

/-! # S2040 qVPlace split/descent first missing

Layer (1) asks for a norm-preserving ring equivalence
`Completion (qVPlace T b) ≃+* Completion (QPlace v)`.  The actual qVPlace is
`qVFamTensorPlace T b`, a finite extension of Q_p; the source files do not
assert that its rational residue degree or ramification index is one
(`BadPlaceRationalDegreeActual` explicitly refuses to fake rationalDegree = 1).
This file records the exact split/descent lemmas still missing and assembles
layer (1) only from explicit split data. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2040QVPlaceSplitActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlaceRationalDegreeActual
open LeanFormal.IUT.XiFPaper.QVFamTensorBlockAlignmentActual
open LeanFormal.IUT.XiFPaper.S2046CompletionOUnitsActual
open LeanFormal.IUT.XiFPaper.S2040NormBridgeS2056Actual
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual

universe u

/-- The actual qVPlace is the qVFamTensorPlace. -/
theorem S2040qVPlace_eq_qVFamTensorPlace
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    qVPlace (l := l) T b = qVFamTensorPlace T b := rfl

/-- Exact missing split/descent lemma: the qVPlace rational residue degree is
one.  This is not asserted by the source; `BadPlaceRationalDegreeActual` keeps
the normalized-source reduction conditional on it. -/
def S2040QVPlaceDegreeOneRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  qVFamTensorRationalDegree T b = 1

/-- Exact missing split/descent lemma: the qVPlace is unramified over Q_p. -/
def S2040QVPlaceUnramifiedRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  localRamificationIndex (k := ℚ) (qVFamTensorPlace T b) = 1

/-- The full missing split package: degree one plus unramified, together with a
norm-preserving completion equivalence to a rational QPlace. -/
structure S2040QVPlaceSplitPackage
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  v : FinitePrimePlace 2 7
  completionEquiv :
    Completion (qVPlace (l := l) T b) ≃+* Completion (QPlace v)
  completion_isometry :
    ∀ x : Completion (qVPlace (l := l) T b),
      ‖completionEquiv x‖ = ‖x‖
  degree_one : S2040QVPlaceDegreeOneRequired T b
  unramified : S2040QVPlaceUnramifiedRequired T b

/-- The package is layer (1). -/
noncomputable def S2040QVPlaceSplitDataOfPackage
    {T : SourceNativeInitialThetaData.{0} l}
    {b : Bad (nativePlaceSelection T)}
    (P : S2040QVPlaceSplitPackage T b) :
    S2040QVPlaceSplitData T b :=
  { v := P.v
    completionEquiv := P.completionEquiv
    completion_isometry := P.completion_isometry }

#check S2040qVPlace_eq_qVFamTensorPlace
#check S2040QVPlaceDegreeOneRequired
#check S2040QVPlaceUnramifiedRequired
#check S2040QVPlaceSplitPackage
#check S2040QVPlaceSplitDataOfPackage

end LeanFormal.IUT.XiFPaper.S2040QVPlaceSplitActual
end
