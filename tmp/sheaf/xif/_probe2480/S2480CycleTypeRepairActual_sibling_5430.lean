import tmp.sheaf.xif.paper.S2203D5RangeActual
import tmp.sheaf.xif.paper.S2364D5GroupRouteActual
import tmp.sheaf.xif.paper.S1894D5LargeImageActual
import tmp.sheaf.xif.paper.S2132FrobCycleActual
import tmp.sheaf.xif.paper.S1987D5LargeImageFiveActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2480CycleTypeRepairActual

open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S2364D5GroupRouteActual
open LeanFormal.IUT.XiFPaper.S1894D5LargeImageActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

/-- The actual range cycle-type target. -/
def S2480Target : Prop := S2203RangeCycleTypeRequired S1982Basis

theorem S2480Target_iff_range :
    S2480Target ↔ HasCycleType102
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range :=
  Iff.rfl

/-- Conjugation preserves pair cycle type. -/
theorem S2480cycleType_pairPermHom_conj (c g : GL2) :
    (pairPermHom (c * g * c⁻¹)).cycleType = (pairPermHom g).cycleType := by
  rw [map_mul, map_mul, map_inv]
  exact Equiv.Perm.cycleType_conj

/-- Cycle type (10,2) is invariant under conjugating the subgroup. -/
theorem S2480HasCycleType102_map_conj (c : GL2) (H : Subgroup GL2) :
    HasCycleType102 (Subgroup.map (MulAut.conj c).toMonoidHom H) ↔ HasCycleType102 H := by
  constructor
  · rintro ⟨h, hh, hc⟩
    rw [Subgroup.mem_map] at hh
    obtain ⟨g, hg, hgk⟩ := hh
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hgk
    refine ⟨g, hg, ?_⟩
    rw [← S2480cycleType_pairPermHom_conj c g]
    exact hgk ▸ hc
  · rintro ⟨g, hg, hc⟩
    refine ⟨c * g * c⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_map]
      exact ⟨g, hg, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    · rw [S2480cycleType_pairPermHom_conj]
      exact hc

/-- The cycle-type hypothesis is basis-independent. -/
theorem S2480RangeCycleType_congr (b b' : S1725TorsionBasis S1987Five) :
    HasCycleType102
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range ↔
      HasCycleType102
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b').range := by
  rw [S1894MatrixRep_range_conj S1987Five b b']
  exact (S2480HasCycleType102_map_conj
    (S1894BasisChangeGL S1987Five b b')
    (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range).symm

theorem S2480Target_iff_basis (b : S1725TorsionBasis S1987Five) :
    S2480Target ↔ HasCycleType102
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range :=
  S2480Target_iff_range.trans (S2480RangeCycleType_congr S1982Basis b)

theorem S2480Target_iff_forall_basis :
    S2480Target ↔ ∀ b : S1725TorsionBasis S1987Five,
      HasCycleType102
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range := by
  constructor
  · intro h b; exact (S2480Target_iff_basis b).mp h
  · intro h; exact (S2480Target_iff_basis S1982Basis).mpr (h S1982Basis)

theorem S2480Target_iff_exists_basis :
    S2480Target ↔ ∃ b : S1725TorsionBasis S1987Five,
      HasCycleType102
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range := by
  constructor
  · intro h; exact ⟨S1982Basis, (S2480Target_iff_basis S1982Basis).mp h⟩
  · rintro ⟨b, hb⟩; exact (S2480Target_iff_basis b).mpr hb

/-- The target as existence of a Galois element with pair cycle type (10,2). -/
theorem S2480Target_iff_exists_sigma :
    S2480Target ↔ ∃ σ : S1725AbsoluteGalois,
      (pairPermHom
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ)).cycleType =
          ({10, 2} : Multiset ℕ) := by
  rw [S2480Target_iff_range]
  change (∃ h : GL (Fin 2) (ZMod S1987Five.value),
      h ∈ (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range ∧
        (pairPermHom h).cycleType = ({10, 2} : Multiset ℕ)) ↔ _
  constructor
  · rintro ⟨h, hh, hc⟩
    obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hh
    exact ⟨σ, hc⟩
  · rintro ⟨σ, hc⟩
    exact ⟨_, MonoidHom.mem_range.mpr ⟨σ, rfl⟩, hc⟩

/-- Exact minimal missing: an actual Galois element with pair cycle type (10,2). -/
def S2480FirstMissing : Prop :=
  ∃ σ : S1725AbsoluteGalois,
    (pairPermHom
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ)).cycleType =
        ({10, 2} : Multiset ℕ)

theorem S2480FirstMissing_iff_target : S2480FirstMissing ↔ S2480Target :=
  S2480Target_iff_exists_sigma.symm

theorem S2480Target_of_firstMissing (h : S2480FirstMissing) : S2480Target :=
  S2480Target_iff_exists_sigma.mpr h

/-- With actual range pair transitivity, the minimal missing gives D5. -/
theorem S2480D5LargeImageFive_of_firstMissing_and_pair
    (h : S2480FirstMissing)
    (hpair : PairTransitive
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range) :
    S1987D5LargeImageFive :=
  S2203D5LargeImageFive_of_rangeHypotheses S1982Basis
    (S2480Target_of_firstMissing h) hpair

end LeanFormal.IUT.XiFPaper.S2480CycleTypeRepairActual

end
