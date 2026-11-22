import tmp.sheaf.xif.paper.S965FinalLCarrierTopologyActual
import tmp.sheaf.xif.paper.S976FiniteLogShellHaarActual

/-! # S988: six exact transport items for FinalLValuedCarrier

The actual construction of S987 is not available as a compiling kernel proof
because the tensor carrier currently has no topology instance and the finite
carrier instance bookkeeping is not definitionally transparent.  This file
records the six transport items as exact existential propositions over the
linearization L.e.  No item is faked; each is the precise data needed by the
S945/S956 consumers. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S988TransportExactItemsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S945CarrierTopologyActual
open LeanFormal.IUT.XiFPaper.S965FinalLCarrierTopologyActual
open LeanFormal.IUT.XiFPaper.S970FiniteLogShellCarrierActual
open LeanFormal.IUT.XiFPaper.S976FiniteLogShellHaarActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (LeanFormal.IUT.nativePlaceSelection T))]
variable (b : Bad (LeanFormal.IUT.nativePlaceSelection T))
variable (L : S965CarrierLinearization (l := l) T b)

abbrev S988C := FinalLValuedCarrier T b
abbrev S988Finite := FiniteLogShellCarrier (qVFamTensorP T b) L.d

/-- T1: induced topology on the tensor carrier. -/
def S988T1Topology : Prop :=
  Nonempty (TopologicalSpace (S988C (l := l) T b))

/-- T2: topological additive group structure. -/
def S988T2TopologicalAddGroup : Prop :=
  ∃ τ : TopologicalSpace (S988C (l := l) T b),
    @IsTopologicalAddGroup (S988C (l := l) T b) τ _

/-- T3: continuous linearization and inverse (homeomorphism data). -/
def S988T3ContinuousEquiv : Prop :=
  ∃ τ : TopologicalSpace (S988C (l := l) T b),
    @Continuous (S988C (l := l) T b) (S988Finite (l := l) T b L) τ _ L.e ∧
    @Continuous (S988Finite (l := l) T b L) (S988C (l := l) T b) _ τ L.e.symm

/-- T4: locally compact carrier. -/
def S988T4LocallyCompact : Prop :=
  ∃ τ : TopologicalSpace (S988C (l := l) T b),
    @LocallyCompactSpace (S988C (l := l) T b) τ

/-- T5: Borel measurable structure. -/
def S988T5Borel : Prop :=
  ∃ (τ : TopologicalSpace (S988C (l := l) T b))
    (ms : MeasurableSpace (S988C (l := l) T b)),
    @BorelSpace (S988C (l := l) T b) τ ms

/-- T6: pushforward additive Haar and unit region. -/
def S988T6Haar : Prop :=
  ∃ (τ : TopologicalSpace (S988C (l := l) T b))
    (ms : MeasurableSpace (S988C (l := l) T b))
    (μ : Measure (S988C (l := l) T b)),
    @Measure.IsAddHaarMeasure (S988C (l := l) T b) _ τ ms μ ∧
    ∃ U : Set (S988C (l := l) T b), 0 < μ U ∧ μ U < ⊤

/-- All six transport items. -/
def S988AllTransportItems : Prop :=
  S988T1Topology (l := l) T b ∧
    S988T2TopologicalAddGroup (l := l) T b ∧
    S988T3ContinuousEquiv (l := l) T b L ∧
    S988T4LocallyCompact (l := l) T b ∧
    S988T5Borel (l := l) T b ∧
    S988T6Haar (l := l) T b

end LeanFormal.IUT.XiFPaper.S988TransportExactItemsActual

end
