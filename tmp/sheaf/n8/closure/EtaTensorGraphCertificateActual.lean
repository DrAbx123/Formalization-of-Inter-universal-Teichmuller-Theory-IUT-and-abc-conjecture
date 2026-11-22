import tmp.sheaf.n8.closure.EtaTensorLatticeImageActual
import tmp.sheaf.n8.closure.FiniteObservationHull

/-!
# EtaTensorGraphCertificateActual

Actual set-level graph certificate for the nonintegral tensor edge
`T_g : Lu → Lv`.  The finite-observation Theorem C interface requires
`Z_p`-submodule lattices and an automorphism; the current actual data gives
a `Q_p`-linear edge map between actual sets, so that interface gap is
recorded explicitly.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaTensorGraphCertificateActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaTensorSplitActual
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphEdgeActual
open LeanFormal.IUT.N8Closure.EtaTensorLatticeImageActual
open LeanFormal.IUT.N8Closure.FiniteObservationHull
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField TensorProduct

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

/-- Actual reference integer ring used for the lattice images. -/
def referenceIntegers : Set (Kf X) := (Integers (Kf X) : Set (Kf X))

/-- Actual source vertex lattice. -/
def vertexSource : Set (E X) := Lu X

/-- Actual target vertex lattice. -/
def vertexTarget : Set (E X) := Lv X (gNonIntegral X)

/-- Actual edge map `T_g` from source to target on the source lattice. -/
def edgeAction : E X →ₗ[ℚ_[nativePrime X]] E X :=
  graphAction X (gNonIntegral X)

/-- Set-level inner/outer hull certificate: the actual edge image of the
source lattice is contained in the target lattice. -/
def TensorSetHullCertificate (X : N8NativeInput l) : Prop :=
  vertexSource X ⊆ Set.univ ∧
    edgeAction X '' vertexSource X ⊆ vertexTarget X ∧
    (vertexSource X).Nonempty

theorem tensorSetHullCertificate_actual : TensorSetHullCertificate X := by
  refine ⟨Set.subset_univ _, ?_, tensorEdge_actual_nonempty X⟩
  rintro y ⟨x, hx, rfl⟩
  exact (tensorEdge_actual X (gNonIntegral X)) x hx

/-- Exact interface gap: a genuine linear automorphism of `E` realizing the
actual edge map, plus `Z_p`-submodule lattice structures needed by
Theorem C. -/
def MissingTensorAutomorphismInterface (X : N8NativeInput l) : Prop :=
  ∃ (e : E X ≃ₗ[ℚ_[nativePrime X]] E X),
    (e : E X →ₗ[ℚ_[nativePrime X]] E X) = edgeAction X

end LeanFormal.IUT.N8Closure.EtaTensorGraphCertificateActual