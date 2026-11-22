import tmp.sheaf.xif.paper.S2178ActionContinuousActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2164MuActionTowerActual
open LeanFormal.IUT.XiFPaper.S2178ActionContinuousActual
open LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
namespace LeanFormal.IUT.XiFPaper.S2196ActionContinuousProofActual
variable (p : Nat) [Fact (Nat.Prime p)]
local instance s2196UnitsTop : TopologicalSpace ((AlgebraicClosure ℚ_[p])ˣ) := ⊥
local instance s2196UnitsDisc : DiscreteTopology ((AlgebraicClosure ℚ_[p])ˣ) :=
  discreteTopology_bot _
theorem S2196ActionContinuous (n : ℕ) :
    S2164ActionContinuous p n := by
  classical
  unfold S2164ActionContinuous
  letI : TopologicalSpace (S2164Roots p n) := instTopologicalSpaceSubtype
  rw [continuous_def]
  intro U hU
  have hfiber : ∀ ζ : S2164Roots p n,
      IsOpen {q : LocalAbsoluteGalois p × S2164Roots p n |
        S2164RootsActionAut p n q.1 q.2 = ζ} := by
    intro ζ
    have hcontUnits : Continuous (fun q : LocalAbsoluteGalois p × ((AlgebraicClosure ℚ_[p])ˣ) =>
        ((localGaloisUnitsAction p) q.1) q.2) := by
      exact (LocalGaloisKummerAction.action p).continuous_action
    have hpre : IsOpen ((fun q : LocalAbsoluteGalois p × ((AlgebraicClosure ℚ_[p])ˣ) =>
        ((localGaloisUnitsAction p) q.1) q.2) ⁻¹' ({ζ.1} : Set ((AlgebraicClosure ℚ_[p])ˣ))) :=
      hcontUnits.isOpen_preimage _ (isOpen_discrete _)
    have hincl : Continuous (fun q : LocalAbsoluteGalois p × S2164Roots p n =>
        (q.1, (q.2 : (AlgebraicClosure ℚ_[p])ˣ))) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    have hpre' := hincl.isOpen_preimage _ hpre
    convert hpre' using 1
    ext q
    simp [S2164RootsActionAut, S2164RootsMulAut, Subtype.ext_iff]
  have hpre : (fun q : LocalAbsoluteGalois p × S2164Roots p n =>
      S2164RootsActionAut p n q.1 q.2) ⁻¹' U =
      ⋃ ζ ∈ U, {q : LocalAbsoluteGalois p × S2164Roots p n |
        S2164RootsActionAut p n q.1 q.2 = ζ} := by
    ext q
    simp
  rw [hpre]
  have hio : IsOpen (⋃ ζ ∈ U, {q : LocalAbsoluteGalois p × S2164Roots p n |
      S2164RootsActionAut p n q.1 q.2 = ζ}) :=
    isOpen_iUnion fun ζ => isOpen_iUnion fun hζ => hfiber ζ
  convert hio using 1
  · congr 1
    exact S2178TopologyBridge_holds p n
noncomputable def S2196MuActionTower : S2145MuActionTower p :=
  S2164MuActionTowerOfContinuous p (fun n => S2196ActionContinuous p n)
#check S2196ActionContinuous
#check S2196MuActionTower
end LeanFormal.IUT.XiFPaper.S2196ActionContinuousProofActual
end
