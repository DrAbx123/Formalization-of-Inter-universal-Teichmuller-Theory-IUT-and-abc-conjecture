import tmp.sheaf.xif.paper.S2928CorrectedTConstructionActual
import tmp.sheaf.n8.closure.NativeSourceSectionsCuspActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2928CorrectedTConstructionActual
namespace LeanFormal.IUT.XiFPaper.S2932CorrectedCuspConsumerActual

universe u
variable {l : PrimeGeFive}

def nativeEpsilonGeometricCorrected
    (T : SourceNativeInitialThetaDataCorrected) :
    Iut.OrbicurveBoundaryCusp T.source.cK :=
  T.source.epsilon

structure NativeCuspClauseHypothesesCorrected
    (T : SourceNativeInitialThetaDataCorrected) where
  epsilon : Real
  epsilon_positive : 0 < epsilon
  epsilon_nonzero : epsilon ≠ 0
  cuspScale : Real
  cuspScale_positive : 0 < cuspScale
  epsilon_scale_relation : epsilon * cuspScale ≠ 0
  epsilon_compatibility : Prop
  epsilon_compatibility_proved : epsilon_compatibility
  native_epsilon_realization : Prop

def MissingNativeCuspObjectCorrected
    (T : SourceNativeInitialThetaDataCorrected) : Prop :=
  Nonempty (NativeCuspClauseHypothesesCorrected T)

#check SourceNativeInitialThetaDataCorrected
#check nativeEpsilonGeometricCorrected
#check NativeCuspClauseHypothesesCorrected
#check MissingNativeCuspObjectCorrected

end LeanFormal.IUT.XiFPaper.S2932CorrectedCuspConsumerActual