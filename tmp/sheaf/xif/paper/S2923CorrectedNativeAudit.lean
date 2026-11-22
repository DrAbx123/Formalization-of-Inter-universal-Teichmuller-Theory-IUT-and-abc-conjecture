import tmp.sheaf.xif.paper.S2908CorrectedSActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual
namespace LeanFormal.IUT.XiFPaper.S2923CorrectedNativeAudit

universe u
variable {l : PrimeGeFive}

/-- Corrected initial theta tuple: source is the corrected sign-quotient record. -/
structure S2923CorrectedTuple (A : InitialThetaArithmeticData l) where
  fbar : SourceFbarExtension A
  source : SourceSignQuotientDataCorrected A
  xF : Iut.HyperbolicOrbicurve A.F
  xF_eq_source : xF = source.xF
  cK : Iut.HyperbolicOrbicurve A.K
  cK_eq_source : source.cK = cK
  V : Set (NumberFieldPlace A.K)
  V_eq_source : V = source.V
  V_mod_bad : Set (NumberField.FinitePlace A.Fmod)
  V_mod_bad_eq_source : V_mod_bad = source.V_mod_bad
  epsilon : Iut.OrbicurveBoundaryCusp cK
  epsilon_eq_source : epsilon = cK_eq_source ▸ source.epsilon

/-- Corrected source-native data skeleton: tuple is corrected; the six clause
types are opaque because corrected clause A-F types do not exist. -/
structure S2923CorrectedNativeDataSkeleton
    (A : InitialThetaArithmeticData l) where
  tuple : S2923CorrectedTuple A
  clauseAType : Type u
  clauseBType : Type u
  clauseCType : Type u
  clauseDType : Type u
  clauseEType : Type u
  clauseFType : Type u

#check S2923CorrectedTuple
#check S2923CorrectedNativeDataSkeleton
#check SourceInitialThetaTuple
#check SourceNativeInitialThetaData
#check SourceClauseA

end LeanFormal.IUT.XiFPaper.S2923CorrectedNativeAudit