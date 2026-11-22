import tmp.sheaf.xif.paper.S827PaperValueGroupNormCardActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S830ValueGroupNormChainActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S819PaperRootCompletionGeneratorActual
open LeanFormal.IUT.XiFPaper.S827PaperValueGroupNormCardActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The exact minimal chain: frozen norm/valuation card plus ramification
alignment.  Both fields are S827 data; neither is proved in the tree. -/
structure PaperValueGroupNormChain where
  card : PaperNormValuationCard T b
  alignment : PaperRamificationAlignment T b
  characterization : ValueGroupNormCharacterization T b

/-- From the chain one gets S819's value-group characterization. -/
theorem valueGroupNormCharacterization_of_chain
    (C : PaperValueGroupNormChain T b) :
    ValueGroupNormCharacterization T b :=
  C.characterization

/-- Conditional S819 no-go: chain + nonmembership of cRoot in the value group
gives no local completion generator. -/
theorem noLocalGenerator_of_chain_noGo
    (C : PaperValueGroupNormChain T b)
    (hno : PaperRootValueGroupNoGo (l := l) T b) :
    ¬ PaperLocalGeneratorRequired (l := l) T b :=
  noLocalGenerator_of_valueGroupNoGo
    (l := l) (T := T) (b := b) C.characterization hno

/-- Exact minimal missing implication: the frozen S827 card + alignment implies
S819 value-group characterization.  This is recorded as a Prop, not asserted. -/
def PaperValueGroupNormChainGap : Prop :=
  PaperNormValuationCard T b →
  PaperRamificationAlignment T b →
  ValueGroupNormCharacterization T b

def PaperValueGroupNormChainGapRequired : Prop :=
  PaperValueGroupNormChainGap T b

end LeanFormal.IUT.XiFPaper.S830ValueGroupNormChainActual
end