import tmp.sheaf.xif.paper.S806PaperRootHullNonzeroGapsActual

/-! # S837: compactness of the paper root minimal region

paperRootMinimalRegion = F(paperRootCoefficientFamily) * O_hol.
For c = order/(2l) >= 0, the intended p-adic fractional-lattice argument gives
compact open F(c), and F(c)*O_hol = F(c).  The project provides compactness of
submoduleTensorSpan from compact local fractional lattices and compactness of
the holomorphic unit reference, but the assembled product equality/compactness
is not present as a single existing lemma.  This file records the exact
compactness datum and the actual implication to the S806 closedness gap.
No compactness is assumed or fabricated. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S837PaperRootMinimalCompactActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.S806PaperRootHullNonzeroGapsActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Exact compactness requirement for the minimal paper root region. -/
def S837MinimalCompactRequired : Prop :=
  IsCompact (paperRootMinimalRegion (l := l) T b)

/-- Exact openness requirement for the minimal paper root region. -/
def S837MinimalOpenRequired : Prop :=
  IsOpen (paperRootMinimalRegion (l := l) T b)

/-- Compactness supplies the S806 closedness gap. -/
theorem paperRootHullNonzeroClosedGap_of_minimal_compact
    (hcompact : S837MinimalCompactRequired (l := l) T b) :
    PaperRootHullNonzeroClosedGap (l := l) T b :=
  paperRootHullNonzeroClosedGap_of_compact (l := l) T b hcompact

/-- Exact combined compact-open datum needed for the S806/S806 formula route. -/
structure S837MinimalCompactOpenData where
  isCompact : IsCompact (paperRootMinimalRegion (l := l) T b)
  isOpen : IsOpen (paperRootMinimalRegion (l := l) T b)

def S837MinimalCompactOpenRequired : Prop :=
  Nonempty (S837MinimalCompactOpenData (l := l) T b)

/-- Exact requirement still missing: the assembled compactness of
F(c)*O_hol from the existing local fractional-lattice/unit-reference
compactness lemmas. -/
def S837AssemblyLemmaRequired : Prop :=
  IsCompact (paperRootMinimalRegion (l := l) T b)

end LeanFormal.IUT.XiFPaper.S837PaperRootMinimalCompactActual

end
