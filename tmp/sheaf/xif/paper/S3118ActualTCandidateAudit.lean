import tmp.sheaf.xif.paper.S2586IQHullLogVolumeInstantiationActual
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual
import tmp.sheaf.xif.paper.S2757CanonicalGaussianTActual
import tmp.sheaf.xif.paper.S2757SourceCompletionNativeActual
import tmp.sheaf.xif.paper.S2848A6CompletionConditionalActual
import tmp.sheaf.xif.paper.S2928CorrectedTConstructionActual
import tmp.sheaf.xif.paper.S1494NativeArithmeticRootActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.XiFPaper.S2757CanonicalGaussianTActual
open LeanFormal.IUT.XiFPaper.S2757SourceCompletionNativeActual
open LeanFormal.IUT.XiFPaper.S2848A6CompletionConditionalActual
open LeanFormal.IUT.XiFPaper.S2928CorrectedTConstructionActual
open LeanFormal.IUT.XiFPaper.S1494NativeArithmeticRootActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3118ActualTCandidateAudit

/-- Target: an actual native initial Theta datum at l = 5. -/
def S3118HasActualT : Prop :=
  Nonempty (SourceNativeInitialThetaData.{0} fiveLabel)

/-- S2586 is available for any T and b once the two measurable instances are
supplied. -/
theorem S3118S2586InterfaceOfT
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    (b : Bad (nativePlaceSelection T))
    [MeasurableSpace (qVFamTensorBlock T b)]
    [BorelSpace (qVFamTensorBlock T b)] :
    Nonempty (IQHullLogVolumeInterface (qVFamTensorBlock T b)) :=
  ⟨S2586IQHullLogVolumeInterface T b⟩

/-- Candidate 2: canonical Gaussian T from a SourceCompletion. -/
def S3118CandidateGaussian : Prop :=
  ∃ (C : SourceCompletion.{0} fiveLabel)
    (h : C.arithmetic = gaussianInitialThetaArithmeticData fiveLabel),
    Nonempty (SourceNativeInitialThetaData.{0} fiveLabel)


/-- Direct S2586 feed from the S2757 native T candidate. -/
theorem S3118S2586OfS2757
    (A : InitialThetaArithmeticData.{0} fiveLabel)
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A)
    (assembly : SourceClauseAssembly.{0} A (G.toSourceSignQuotientData P))
    (b : Bad (nativePlaceSelection (S2757NativeT A G P assembly)))
    [MeasurableSpace (qVFamTensorBlock (S2757NativeT A G P assembly) b)]
    [BorelSpace (qVFamTensorBlock (S2757NativeT A G P assembly) b)] :
    Nonempty (IQHullLogVolumeInterface
      (qVFamTensorBlock (S2757NativeT A G P assembly) b)) :=
  ⟨S2586IQHullLogVolumeInterface (S2757NativeT A G P assembly) b⟩


#check S3118HasActualT
#check S3118S2586InterfaceOfT
#check S2757CanonicalGaussianT
#check S3118S2586OfS2757
#check S2848NativeData
#check S2928CorrectedT
#check paperNativeRoot_nonempty_iff_clauseAssembly

end LeanFormal.IUT.XiFPaper.S3118ActualTCandidateAudit
end