import tmp.sheaf.xif.paper.S893RootStackDVRInstanceActual

/-! # S902: remaining ambient/NormedAlgebra instances for E

Ambient algebraic closure ultrametricity is transported from
SourceAlgebraicClosure.  Qp-NormedAlgebra on L and E is obtained by
restrictScalars.  The DVR instance and uniformizer construction are kept in
S902RootStackDVRUniformizerActual to avoid one oversized elaboration unit. -/

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal Valued
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S902RootStackDVRInstancesActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S831StackHaarDimensionActual
open LeanFormal.IUT.XiFPaper.S893RootStackDVRInstanceActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Ambient algebraic closure is ultrametric. -/
noncomputable instance s902AmbientUltrametric :
    IsUltrametricDist (rootNormedAmbient T b) :=
  inferInstanceAs (IsUltrametricDist
    (SourceAlgebraicClosure (qVFamTensorPlace T b)))

/-- Subtype ultrametric instance on E. -/
noncomputable instance s902RootStackUltrametric :
    IsUltrametricDist (rootStackExtension T b) :=
  inferInstance

/-- Qp-NormedAlgebra on L. -/
noncomputable instance s902NormedAlgebraQpL :
    NormedAlgebra ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
  NormedAlgebra.restrictScalars ℚ_[(qVFamTensorP T b)] (rootBase T b)
    (rootNormedExtension T b)

/-- Exact remaining L-NormedAlgebra on E (needed before Qp E). -/
def S902NormedAlgebraLERequired : Prop :=
  Nonempty (NormedAlgebra (rootNormedExtension T b) (rootStackExtension T b))

/-- Exact remaining Qp-NormedAlgebra on E. -/
def S902NormedAlgebraQpERequired : Prop :=
  Nonempty (NormedAlgebra ℚ_[(qVFamTensorP T b)] (rootStackExtension T b))

/-- Two of the three S893 inputs are actual: ambient ultrametricity and
Qp-NormedAlgebra on L.  The remaining exact input is Qp-NormedAlgebra on E,
equivalently the L-NormedAlgebra structure plus restrictScalars. -/
theorem s902PartialRootStackDVRInstanceInputs :
    S893AmbientUltrametricRequired (l := l) T b ∧
      S893NormedAlgebraQpLRequired (l := l) T b :=
  ⟨s902AmbientUltrametric (l := l) T b,
    ⟨s902NormedAlgebraQpL (l := l) T b⟩⟩

end LeanFormal.IUT.XiFPaper.S902RootStackDVRInstancesActual

end
