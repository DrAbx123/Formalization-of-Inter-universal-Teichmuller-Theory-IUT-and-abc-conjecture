import tmp.sheaf.xif.paper.Mzk1ThetaRootCarrierActual
import tmp.sheaf.xif.paper.Mzk1TensorCoreWitnessActual
import tmp.sheaf.xif.paper.Mzk1P3TensorCoreActual
/-! #6 THETA-D re-anchor to native carriers (no C3 inhabitant).

`ThetaRootCarrier` is the root-extension product carrier, definitionally a
dependent product over bad places; the tensor core supplies the field-product
projection `tensorCoreWitness.equiv`; the remaining construction datum is the
block/product alignment `BlockProductAlignmentData`. -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P3NativeDReanchorActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ThetaRootCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1TensorCoreWitnessActual
open LeanFormal.IUT.XiFPaper.Mzk1P3TensorCoreActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Native theta-D carrier: definitionally the dependent product of root
extensions over bad places (no C3). -/
theorem thetaRootCarrier_eq_pi :
    ThetaRootCarrier T = ((b : Bad (nativePlaceSelection T)) → rootNormedExtension T b) := rfl
/-- Exact construction datum remaining for the #6 native D-side bridge: the
field factors `J` of the tensor core must be identified with the bad places and
each factor with the corresponding root extension. -/
structure BlockProductAlignmentData
    {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {V : ι → Type} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : ι) → V i) where
  JEquiv : (tensorCoreWitness places tuple).J ≃ Bad (nativePlaceSelection T)
  factorEquiv : ∀ j, (tensorCoreWitness places tuple).E j ≃
    rootNormedExtension T (JEquiv j)
end LeanFormal.IUT.XiFPaper.Mzk1P3NativeDReanchorActual
end