import tmp.sheaf.xif.paper.S2778LargeImageFromMatricesActual
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2783QuadraticBaseChangeLargeImage

open LeanFormal.IUT

/-- Group-theoretic core: if P ≤ M, L ≤ M, P is perfect, and L has
commutative quotient in M, then P ≤ L. In the quadratic base-change case
the quotient is C2 (index two), hence commutative. -/
theorem S2783_sl2_le_of_commutative_quotient
    {G : Type*} [Group G] (P M L : Subgroup G)
    (hPM : P ≤ M) (hLM : L ≤ M)
    (hPperfect : ⁅P, P⁆ = P)
    (hnormal : (L.subgroupOf M).Normal)
    (hcomm : IsMulCommutative (M ⧸ L.subgroupOf M)) :
    P ≤ L := by
  classical
  letI := hnormal
  have hcommut : ⁅M, M⁆ ≤ L := by
    have h := (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (G := M) (N := L.subgroupOf M)).mp hcomm
    have hmap : (_root_.commutator M).map M.subtype ≤ L := by
      intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      exact (Subgroup.mem_subgroupOf).mp (h hy)
    simpa [Subgroup.map_subtype_commutator] using hmap
  calc
    P = ⁅P, P⁆ := hPperfect.symm
    _ ≤ ⁅M, M⁆ := Subgroup.commutator_mono hPM hPM
    _ ≤ L := hcommut

/-- Explicit group-theoretic interface for the quadratic base change: rho is
the mod-5 representation, N the index-two open subgroup, rho(N) the restricted
image. -/
structure S2783QuadraticBaseChangeData (Γ : Type*) [Group Γ] where
  rho : Γ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 5)
  N : Subgroup Γ
  hSL : Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))) ≤ rho.range
  hperfect : ⁅Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))),
      Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)))⁆ =
    Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)))
  [hnormal : ((N.map rho).subgroupOf rho.range).Normal]
  hcomm : IsMulCommutative (rho.range ⧸ (N.map rho).subgroupOf rho.range)

/-- Conditional quadratic base-change large-image transfer. -/
theorem S2783_sl2_le_restricted_range
    {Γ : Type*} [Group Γ] (D : S2783QuadraticBaseChangeData Γ) :
    Subgroup.map Matrix.SpecialLinearGroup.toGL
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))) ≤
      D.N.map D.rho :=
  S2783_sl2_le_of_commutative_quotient
    (Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))))
    D.rho.range (D.N.map D.rho) D.hSL (Subgroup.map_le_range D.rho D.N) D.hperfect
    D.hnormal D.hcomm

/-- Exact missing SL2 perfectness input (not proved in this file). -/
def S2783SL2Perfect : Prop :=
  ⁅Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))),
      Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)))⁆ =
    Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)))

/-- Exact missing quadratic-restriction input. -/
def S2783QuadraticRestrictionCompatible
    {Γ : Type*} [Group Γ]
    (rho : Γ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 5))
    (N : Subgroup Γ) : Prop :=
  ∃ hnormal : ((N.map rho).subgroupOf rho.range).Normal,
    letI := hnormal
    IsMulCommutative (rho.range ⧸ (N.map rho).subgroupOf rho.range)

#check S2783_sl2_le_of_commutative_quotient
#check S2783_sl2_le_restricted_range
#check S2783SL2Perfect
#check S2783QuadraticRestrictionCompatible
#print axioms S2783_sl2_le_restricted_range

end LeanFormal.IUT.XiFPaper.S2783QuadraticBaseChangeLargeImage
end
