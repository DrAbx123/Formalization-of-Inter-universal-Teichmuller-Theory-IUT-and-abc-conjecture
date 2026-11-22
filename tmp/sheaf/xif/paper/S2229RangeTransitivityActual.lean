import tmp.sheaf.xif.paper.S2221AffinePairTransitivityActual
import tmp.sheaf.xif.paper.S2218RangePairTransitiveActual
import tmp.sheaf.xif.paper.S2203D5RangeActual
import tmp.sheaf.xif.paper.S1987D5LargeImageFiveActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2229RangeTransitivityActual

open LeanFormal.IUT.XiFPaper.S2221AffinePairTransitivityActual
open LeanFormal.IUT.XiFPaper.S2218RangePairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual

/-- The actual Galois group of the algebraic closure of F'. -/
abbrev S2229GaloisGroup : Type :=
  AlgebraicClosure S1720Field ≃ₐ[S1720Field] AlgebraicClosure S1720Field

/-- Transport of `ZMod S1987Five.value` to `ZMod 5`. -/
noncomputable def S2229ZModEquiv : ZMod S1987Five.value ≃+* ZMod 5 :=
  ZMod.ringEquivCongr (by rfl : S1987Five.value = 5)

/-- Transport of the matrix group `GL (Fin 2) (ZMod S1987Five.value)` to
`GL2 = GL (Fin 2) (ZMod 5)`. -/
noncomputable def S2229GLMap :
    GL (Fin 2) (ZMod S1987Five.value) →* GL2 :=
  Matrix.GeneralLinearGroup.map S2229ZModEquiv.toRingHom

/-- The transferred actual mod-5 range, as a subgroup of GL2. -/
noncomputable def S2229TransferredRange
    (b : S1725TorsionBasis S1987Five) : Subgroup GL2 :=
  (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range.map
    S2229GLMap

/-- The actual Galois action on affine pairs, using the transported range. -/
noncomputable def S2229GaloisPairPerm
    (b : S1725TorsionBasis S1987Five) (σ : S2229GaloisGroup) :
    Equiv.Perm S2056Pair :=
  S2218PairPerm
    (S2229GLMap ((S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b) σ))

/-- Actual Galois transitivity on the twelve affine pairs at the transported
range. -/
def S2229GaloisPairTransitive
    (b : S1725TorsionBasis S1987Five) : Prop :=
  ∀ x y : S2056Pair, ∃ σ : S2229GaloisGroup,
    S2229GaloisPairPerm b σ x = y

/-- Actual equivalence: Galois transitivity is exactly transitivity of the
transferred range under the S2218 action. -/
theorem S2229GaloisPairTransitive_iff
    (b : S1725TorsionBasis S1987Five) :
    S2229GaloisPairTransitive b ↔
      S2218AffinePairTransitive (S2229TransferredRange b) := by
  constructor
  · intro h x y
    obtain ⟨σ, hσ⟩ := h x y
    refine ⟨S2229GLMap ((S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b) σ),
      ⟨_, MonoidHom.mem_range.mpr ⟨σ, rfl⟩, rfl⟩, hσ⟩
  · intro h x y
    obtain ⟨g, hg, hgxy⟩ := h x y
    rcases (Subgroup.mem_map.mp hg) with ⟨h, hh, hgh⟩
    obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp hh
    refine ⟨σ, ?_⟩
    unfold S2229GaloisPairPerm
    rw [hσ, hgh]
    exact hgxy

/-- Exact first missing: actual Galois transitivity on affine pairs after the
GL transport. -/
def S2229ActualGaloisPairTransitiveRequired : Prop :=
  S2229GaloisPairTransitive S1982Basis

/-- Exact compatibility target: transitivity of the transferred range must be
identified with the S2203 pair-transitivity hypothesis. -/
def S2229TransferredPairCompatibilityRequired : Prop :=
  S2218AffinePairTransitive (S2229TransferredRange S1982Basis) ↔
    S2203RangePairTransitiveRequired S1982Basis

/-- Conditional assembly of the S2203 pair-transitivity hypothesis from the
transported transitivity and the compatibility target. -/
theorem S2229RangePairTransitive_of_transferred
    (h : S2218AffinePairTransitive (S2229TransferredRange S1982Basis))
    (hcomp : S2229TransferredPairCompatibilityRequired) :
    S2203RangePairTransitiveRequired S1982Basis :=
  hcomp.mp h

/-- Conditional D5 assembly from the transported Galois transitivity, its
compatibility, and the cycle-type hypothesis. -/
theorem S2229D5LargeImageFive_of_transferred
    (h : S2229ActualGaloisPairTransitiveRequired)
    (hcomp : S2229TransferredPairCompatibilityRequired)
    (hcycle : S2203RangeCycleTypeRequired S1982Basis) :
    S1987D5LargeImageFive :=
  S2203D5LargeImageFive_of_rangeHypotheses S1982Basis hcycle
    (S2229RangePairTransitive_of_transferred
      ((S2229GaloisPairTransitive_iff S1982Basis).mp h) hcomp)

end LeanFormal.IUT.XiFPaper.S2229RangeTransitivityActual

end
