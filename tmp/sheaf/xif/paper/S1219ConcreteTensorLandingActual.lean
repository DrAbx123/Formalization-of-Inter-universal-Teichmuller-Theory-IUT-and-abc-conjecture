import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorFieldDecomposition
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput

/-! # S1219: diagonal finite tensor insertion nonzero and concrete tensor landing

For a finite index type and a nonzero `z`, the diagonal pure tensor
`⨂_i z` is nonzero.  Applied to the concrete one-place-per-index tensor block
of `V = FinitePrimePlace 2 7`, this gives an actual tensor landing
`CommonPrimeCompletion place → ConcreteTensorBlock` with the tensor unit taken
to be the diagonal insertion of the q candidate, not forced to 1. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1219ConcreteTensorLandingActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor

/-- The diagonal pure tensor of a finite family of the same nonzero element is
nonzero. -/
theorem finitePadicTensorTprod_diagonal_ne_zero
    {p : Nat} [Fact p.Prime] {ι : Type*} [Fintype ι] {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℚ_[p] M] [FiniteDimensional ℚ_[p] M]
    {z : M} (hz : z ≠ 0) :
    finitePadicTensorTprod (p := p) (fun _ : ι => M) (fun _ => z) ≠ 0 := by
  intro hzero
  have hcoord := congrArg (finitePadicTensorCoordinates (p := p) (fun _ : ι => M)) hzero
  have hex : ∀ _ : ι, ∃ k : Fin (Module.finrank ℚ_[p] M),
      (Module.finBasis ℚ_[p] M).repr z k ≠ 0 := by
    intro _
    by_contra h
    push_neg at h
    apply hz
    apply (Module.finBasis ℚ_[p] M).repr.injective
    ext k
    simpa using h k
  let k : ι → Fin (Module.finrank ℚ_[p] M) := fun i => Classical.choose (hex i)
  have hk : ∀ i, (Module.finBasis ℚ_[p] M).repr z (k i) ≠ 0 :=
    fun i => Classical.choose_spec (hex i)
  have hprod : (∏ i : ι, (Module.finBasis ℚ_[p] M).repr z (k i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hk i)
  have hval := congrFun hcoord k
  simp only [finitePadicTensorCoordinates_tprod, map_zero, Pi.zero_apply] at hval
  exact hprod hval

universe upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- Concrete tensor index: `FinitePrimePlace 2 7`. -/
abbrev ConcreteIndex : Type := FinitePrimePlace 2 7
/-- Concrete one-factor place index. -/
abbrev ConcretePlaceIndex (i : ConcreteIndex) : Type := Unit
/-- Concrete tensor places: the supplied actual place at every index. -/
noncomputable def concretePlaces (i : ConcreteIndex) (a : ConcretePlaceIndex i) :
    FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p := place
/-- Concrete tensor tuple: the unique point. -/
noncomputable def concreteTuple (i : ConcreteIndex) : ConcretePlaceIndex i := ()
/-- Concrete tensor block over all concrete indices. -/
abbrev ConcreteBlock (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p) : Type :=
  FinitePadicTensor (p := p)
    (fun _ : ConcreteIndex => CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)

/-- Actual diagonal tensor landing: `z ↦ ⨂_i z`. -/
noncomputable def concreteTensorLanding (z : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) :
    ConcreteBlock I place :=
  finitePadicTensorTprod (p := p)
    (M := fun _ : ConcreteIndex => CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)
    (fun _ => z)

theorem concreteTensorLanding_apply
    (z : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) :
    concreteTensorLanding I place z =
      finitePadicTensorTprod (p := p)
        (M := fun _ : ConcreteIndex =>
          CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)
        (fun _ => z) := rfl

/-- The diagonal landing is nonzero on a nonzero q. -/
theorem concreteTensorLanding_ne_zero
    (q : FinitePlaceQCandidate place.val) (hq : q.q ≠ 0) :
    concreteTensorLanding I place q.q ≠ 0 :=
  finitePadicTensorTprod_diagonal_ne_zero (p := p) (ι := ConcreteIndex)
    (M := CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) hq

-- Exact gap: `ConcreteTensorLandingData` also needs
-- `tensorUnit : (ConcreteBlock I place)ˣ` with a GroupWithZero/Units structure on
-- the tensor block.  The current tensor block carries AddCommGroup/Module but no
-- GroupWithZero, so `Units.mk0` is not available; no tensorUnit is fabricated.

end LeanFormal.IUT.XiFPaper.S1219ConcreteTensorLandingActual
end
