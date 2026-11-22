import tmp.sheaf.xif.paper.S2390H1ComparisonDoneActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
open LeanFormal.IUT
open KummerTheory
open LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2196ActionContinuousProofActual
open LeanFormal.IUT.XiFPaper.S2204ActualH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2384H1ComparisonActual
open LeanFormal.IUT.XiFPaper.S2390H1ComparisonDoneActual
namespace LeanFormal.IUT.XiFPaper.S2399H1QuotientActual
variable (p : Nat) [Fact (Nat.Prime p)] (n : ℕ)
local instance s2399MulDistrib :
    MulDistribMulAction (LocalAbsoluteGalois p) (S2145Coeff p n) :=
  MulDistribMulAction.compHom (S2145Coeff p n)
    ((S2196MuActionTower p).actn n).automorphism
/-- The external coboundary relation corresponding to an internal twist. -/
theorem S2399Twist_external_coboundary
    (z : Iut.ContinuousOneCocycle
      ((S2196MuActionTower p).actn n))
    (a : S2145Coeff p n) :
    groupCohomology.IsMulCoboundary₁
      (fun g : LocalAbsoluteGalois p =>
        (S2390ToExternalCocycle p n z).1 g /
          (S2390ToExternalCocycle p n (z.twist a)).1 g) := by
  refine ⟨a⁻¹, ?_⟩
  intro g
  simp only [S2390ToExternalCocycle, Iut.ContinuousOneCocycle.twist_apply]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  simp [mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
  rfl
/-- Internal twists give equal external H^1 classes. -/
theorem S2399_mk_twist_eq
    (z : Iut.ContinuousOneCocycle ((S2196MuActionTower p).actn n))
    (a : S2145Coeff p n) :
    ContH1.mk (S2390ToExternalCocycle p n z) =
      ContH1.mk (S2390ToExternalCocycle p n (z.twist a)) :=
  (ContH1.mk_eq_mk_iff _ _).mpr
    (S2399Twist_external_coboundary p n z a)
/-- The quotient-level map from the internal H^1 to the external H^1. -/
noncomputable def S2399ToExternal :
    S2204H1 p n → ContH1 (LocalAbsoluteGalois p) (S2145Coeff p n) :=
  Quotient.lift
    (fun z => ContH1.mk (S2390ToExternalCocycle p n z))
    (by
      intro z w h
      rcases h with ⟨a, rfl⟩
      exact S2399_mk_twist_eq p n z a)
#check S2399Twist_external_coboundary
#check S2399_mk_twist_eq
#check S2399ToExternal
end LeanFormal.IUT.XiFPaper.S2399H1QuotientActual
end
