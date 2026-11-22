import tmp.sheaf.xif.paper.S819PaperRootCompletionGeneratorActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionNormFormula
/-! # S827: value-group characterization vs the frozen norm/valuation card
S819 reduced the local generator to ValueGroupNormCharacterization.  Mathlib/
the tree prove the equivalence with NormValuationCompatible, but the frozen
card NormalizedCompletionNormValuationFormula is not proved.  This file records
the exact minimal card and the ramification-exponent alignment; no fake norm
formula. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S827PaperValueGroupNormCardActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S819PaperRootCompletionGeneratorActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
/-- The actual finite place underlying the paper root block. -/
abbrev paperValueGroupPlace : NumberField.FinitePlace T.arithmetic.F :=
  qVFamTensorPlace T b
/-- Frozen normalized norm/valuation card at the paper place. -/
def PaperNormValuationCard : Prop :=
  NormalizedCompletionNormValuationFormula (F := T.arithmetic.F)
    (paperValueGroupPlace T b)
/-- The frozen card in logarithmic form. -/
def PaperNormValuationCompatible : Prop :=
  NormValuationCompatible (F := T.arithmetic.F) (paperValueGroupPlace T b)
    (relativeRamificationIndex (k := ℚ) (paperValueGroupPlace T b))
theorem paperNormValuationCard_iff :
    PaperNormValuationCard T b ↔ PaperNormValuationCompatible T b :=
  Iff.rfl
/-- Exact ramification-exponent alignment needed by S819. -/
def PaperRamificationAlignment : Prop :=
  paperRamificationExponent T b =
    relativeRamificationIndex (k := ℚ) (paperValueGroupPlace T b)
/-- Exact minimal data for S819's value-group characterization: the frozen
card plus the ramification alignment.  No inhabitant is asserted. -/
structure PaperValueGroupNormData where
  norm_valuation_card : PaperNormValuationCard T b
  ramification_alignment : PaperRamificationAlignment T b
/-- Exact required card package. -/
def PaperValueGroupNormDataRequired : Prop :=
  Nonempty (PaperValueGroupNormData T b)
/-- The exact minimal lemma that remains: the frozen norm/valuation card at
the paper place.  It is not replaced by an axiom or a fake formula. -/
def PaperValueGroupNormExactLemma : Prop :=
  PaperNormValuationCard T b
end LeanFormal.IUT.XiFPaper.S827PaperValueGroupNormCardActual
