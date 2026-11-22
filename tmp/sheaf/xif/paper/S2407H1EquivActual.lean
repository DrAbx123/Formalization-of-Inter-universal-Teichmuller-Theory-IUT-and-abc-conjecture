import tmp.sheaf.xif.paper.S2399H1QuotientActual
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
open LeanFormal.IUT.XiFPaper.S2399H1QuotientActual
namespace LeanFormal.IUT.XiFPaper.S2407H1EquivActual
variable (p : Nat) [Fact (Nat.Prime p)] (n : ℕ)
local instance s2407MulDistrib :
    MulDistribMulAction (LocalAbsoluteGalois p) (S2145Coeff p n) :=
  MulDistribMulAction.compHom (S2145Coeff p n)
    ((S2196MuActionTower p).actn n).automorphism
/-- External coboundary relation implies the internal cohomologous relation. -/
theorem S2407ExternalCoboundary_to_Cohomologous
    (c d : Iut.ContinuousOneCocycle
      ((S2196MuActionTower p).actn n))
    (h : groupCohomology.IsMulCoboundary₁
      (fun g : LocalAbsoluteGalois p =>
        (S2390ToExternalCocycle p n c).1 g /
          (S2390ToExternalCocycle p n d).1 g)) :
    c.Cohomologous d := by
  rcases h with ⟨x, hx⟩
  refine ⟨x⁻¹, ?_⟩
  apply Iut.ContinuousOneCocycle.ext
  intro g
  have hg := hx g
  simp only [S2390ToExternalCocycle] at hg
  simp only [div_eq_mul_inv] at hg
  change d.toFun g =
    (x⁻¹)⁻¹ * c.toFun g *
      ((S2196MuActionTower p).actn n).act g x⁻¹
  have hsm : g • x = ((S2196MuActionTower p).actn n).act g x :=
    rfl
  rw [hsm] at hg
  rw [Iut.ContinuousGroupAction.act_inv]
  rw [inv_inv]
  calc
    d.toFun g = (c.toFun g * (d.toFun g)⁻¹)⁻¹ * c.toFun g :=
      by group
    _ = (((S2196MuActionTower p).actn n).act g x * x⁻¹)⁻¹ * c.toFun g :=
      by rw [← hg]
    _ = x * c.toFun g *
        (((S2196MuActionTower p).actn n).act g x)⁻¹ := by
      rw [mul_inv_rev, inv_inv]
      ac_rfl
/-- Exact missing: the quotient-level equivalence. -/
structure S2407H1EquivRequired where
  equiv : S2204H1 p n ≃
    ContH1 (LocalAbsoluteGalois p) (S2145Coeff p n)
#check S2407ExternalCoboundary_to_Cohomologous
#check S2407H1EquivRequired
end LeanFormal.IUT.XiFPaper.S2407H1EquivActual
end
