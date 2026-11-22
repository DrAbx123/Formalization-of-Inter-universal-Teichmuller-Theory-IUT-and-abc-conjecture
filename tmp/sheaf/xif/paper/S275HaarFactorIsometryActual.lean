import tmp.sheaf.xif.paper.RootTensorHaarIsometryActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarFactorActual

/-! # S275: block/root Haar factor comparison via the isometry

The actual block/root Haar factors and the isometry are available; this file
records the exact scalar comparison requirement.  No factor equality is
asserted without a transport proof.

No inequality/no fake factor/sorry/axiom/True/PUnit.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S275HaarFactorIsometryActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarFactorActual
open LeanFormal.IUT.XiFPaper.RootTensorThetaHullActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarIsometryActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Actual block/root factor comparison data at a field unit. -/
structure BlockRootHaarFactorComparison (lam : (rootNormedExtension T b)ˣ) where
  blockFactor : ENNReal
  blockFactor_eq : blockFactor =
    (thetaScalingHaarFactor (T := T) (b := b) (lam : rootNormedExtension T b)
      (Units.ne_zero lam) : ENNReal)
  rootFactor : ENNReal
  rootFactor_eq : rootFactor = rootHaarFactor T b lam
  scalar_relation : Prop

def BlockRootHaarFactorComparisonRequired
    (lam : (rootNormedExtension T b)ˣ) : Prop :=
  Nonempty (BlockRootHaarFactorComparison (T := T) (b := b) lam)

end LeanFormal.IUT.XiFPaper.S275HaarFactorIsometryActual

end
