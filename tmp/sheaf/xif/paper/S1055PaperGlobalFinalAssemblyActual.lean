import tmp.sheaf.xif.paper.S1051PaperGlobalFinalActual
import tmp.sheaf.xif.paper.S1052PaperQParameterCardActual
import tmp.sheaf.xif.paper.S1053HullAverageAmbientExactActual
import tmp.sheaf.xif.paper.S1054PaperFinalLinksActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual

-- S1055: final paper-global Cor312 assembly.
-- S1052 actual card (given negativity), S1053 ambient hull exact bridge,
-- S1054 actual finite links (given IPL/SHE/APT).  No classical=paper
-- equality; no fake card/links.

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1055PaperGlobalFinalAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S1051PaperGlobalFinalActual
open LeanFormal.IUT.XiFPaper.S1052PaperQParameterCardActual
open LeanFormal.IUT.XiFPaper.S1053HullAverageAmbientExactActual
open LeanFormal.IUT.XiFPaper.S1054PaperFinalLinksActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory

universe uX uLabel

variable {l : PrimeGeFive}
variable {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]
variable (P : PaperSignedHull X label)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Exact final inputs after S1052/S1053/S1054 are used. -/
structure S1055PaperFinalInput where
  In : S994FiniteInput T
  hneg : S1052PaperGlobalNeg (l := l) T In
  ambient : S1053AmbientHullLogExact (l := l) P T In
  evidence : S1054IPLSHEAPTEvidence

noncomputable def s1055ToS1054
    (H : S1055PaperFinalInput (l := l) P T) :
    S1054PaperFinalInput (l := l) P T where
  In := H.In
  hullavg := s1053HullAverage_of_ambient (l := l) P T H.In H.ambient
  card := s1052PaperQParameterCard (l := l) T H.In H.hneg
  evidence := H.evidence

/-- Final paper-global Cor312Conclusion, actual from the four exact inputs. -/
noncomputable def s1055PaperGlobalFinalCor312
    (H : S1055PaperFinalInput (l := l) P T) :=
  s1054PaperFinalCor312_of_input (l := l) P T (s1055ToS1054 (l := l) P T H)

def S1055FinalAssemblyRequired : Prop :=
  Nonempty (S1055PaperFinalInput (l := l) P T)

#check s1055PaperGlobalFinalCor312
#check S1055PaperFinalInput
#check S1055FinalAssemblyRequired

end LeanFormal.IUT.XiFPaper.S1055PaperGlobalFinalAssemblyActual

end