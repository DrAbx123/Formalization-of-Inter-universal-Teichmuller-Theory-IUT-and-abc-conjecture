import tmp.sheaf.xif.paper.S1962R1AbstractActionActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionIsometry

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped Topology

namespace Probe2

variable {K : Type*} [Field K] [NumberField K]
variable (place : NumberField.FinitePlace K)

-- norm invariance
theorem norm_galois_smul
    (σ : SourceAlgebraicClosure place ≃ₐ[NormalizedCompletion place]
      SourceAlgebraicClosure place) (x : SourceAlgebraicClosure place) :
    ‖σ x‖ = ‖x‖ := by
  rw [show ‖σ x‖ = spectralNorm (PadicScalarField place) (SourceAlgebraicClosure place) (σ x) from rfl,
    show ‖x‖ = spectralNorm (PadicScalarField place) (SourceAlgebraicClosure place) x from rfl]
  exact LeanFormal.IUT.IUTII.Frobenioid.Example36.spectralNorm_algHom_eq
    (K := PadicScalarField place) (A := SourceAlgebraicClosure place)
    (B := SourceAlgebraicClosure place)
    (σ.restrictScalars (PadicScalarField place)) x

end Probe2
