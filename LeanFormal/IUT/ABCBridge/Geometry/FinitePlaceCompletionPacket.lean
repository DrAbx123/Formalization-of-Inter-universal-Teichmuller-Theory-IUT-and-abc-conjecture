import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorFieldDecomposition
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.Etale.Pi

/-!
# A finite arithmetic completion packet over one Qp

Keep every supplied place as a separate direct-sum coordinate. The
finite product is the same additive module via the actual direct-sum
equivalence. It is a finite etale Qp algebra, rather than a field.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

noncomputable section

universe u v

variable {K : Type u} [Field K] [NumberField K]
variable {p : ℕ} [Fact p.Prime] {V : Type v} [Fintype V]

def CompletionPacket (places : V → FinitePlaceAtPrime K p) :=
  (v : V) → CommonPrimeCompletion (places v)

instance completionPacketNormedCommRing (places : V → FinitePlaceAtPrime K p) :
    NormedCommRing (CompletionPacket places) :=
  inferInstanceAs (NormedCommRing ((v : V) → CommonPrimeCompletion (places v)))

instance completionPacketAlgebra (places : V → FinitePlaceAtPrime K p) :
    Algebra ℚ_[p] (CompletionPacket places) :=
  inferInstanceAs (Algebra ℚ_[p] ((v : V) → CommonPrimeCompletion (places v)))

instance completionPacketNormedAlgebra (places : V → FinitePlaceAtPrime K p) :
    NormedAlgebra ℚ_[p] (CompletionPacket places) :=
  inferInstanceAs (NormedAlgebra ℚ_[p] ((v : V) → CommonPrimeCompletion (places v)))

instance completionPacketRatModule (places : V → FinitePlaceAtPrime K p) :
    Module ℚ (CompletionPacket places) :=
  inferInstanceAs (Module ℚ ((v : V) → CommonPrimeCompletion (places v)))

instance completionPacketRatScalarTower (places : V → FinitePlaceAtPrime K p) :
    IsScalarTower ℚ ℚ_[p] (CompletionPacket places) :=
  inferInstanceAs (IsScalarTower ℚ ℚ_[p] ((v : V) → CommonPrimeCompletion (places v)))

instance completionPacketFinite (places : V → FinitePlaceAtPrime K p) :
    FiniteDimensional ℚ_[p] (CompletionPacket places) :=
  inferInstanceAs (FiniteDimensional ℚ_[p] ((v : V) → CommonPrimeCompletion (places v)))

instance completionPacketProper (places : V → FinitePlaceAtPrime K p) :
    ProperSpace (CompletionPacket places) :=
  FiniteDimensional.proper ℚ_[p] (CompletionPacket places)

def completionPacketDirectSumEquiv (places : V → FinitePlaceAtPrime K p) :
    DirectSum V (fun v => CommonPrimeCompletion (places v)) ≃ₗ[ℚ_[p]] CompletionPacket places :=
  DirectSum.linearEquivFunOnFintype ℚ_[p] V _

theorem completionPacketDirectSumEquiv_lof [DecidableEq V]
    (places : V → FinitePlaceAtPrime K p) (v : V) (x : CommonPrimeCompletion (places v)) :
    completionPacketDirectSumEquiv places
      (DirectSum.lof ℚ_[p] V (fun v => CommonPrimeCompletion (places v)) v x) =
      (Pi.single v x : CompletionPacket places) :=
  DirectSum.linearEquivFunOnFintype_lof ℚ_[p]
    (M := fun v => CommonPrimeCompletion (places v)) v x

instance completionPacketEtale (places : V → FinitePlaceAtPrime K p) :
    Algebra.Etale ℚ_[p] (CompletionPacket places) := by
  letI : ∀ v, Algebra.FormallyEtale ℚ_[p] (CommonPrimeCompletion (places v)) :=
    fun v => Algebra.FormallyEtale.of_isSeparable ℚ_[p] (CommonPrimeCompletion (places v))
  letI : ∀ v, Algebra.Etale ℚ_[p] (CommonPrimeCompletion (places v)) :=
    fun _ => ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  exact inferInstanceAs (Algebra.Etale ℚ_[p] ((v : V) → CommonPrimeCompletion (places v)))

end

end LeanFormal.IUT.NumberFieldFinitePlace
