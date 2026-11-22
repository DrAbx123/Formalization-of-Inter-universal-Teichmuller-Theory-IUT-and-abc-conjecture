import tmp.sheaf.xif.paper.S2407H1EquivActual
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
open LeanFormal.IUT.XiFPaper.S2407H1EquivActual
namespace LeanFormal.IUT.XiFPaper.S2410H1EquivDoneActual
variable (p : Nat) [Fact (Nat.Prime p)] (n : ℕ)
local instance s2410MulDistrib :
    MulDistribMulAction (LocalAbsoluteGalois p) (S2145Coeff p n) :=
  MulDistribMulAction.compHom (S2145Coeff p n)
    ((S2196MuActionTower p).actn n).automorphism
/-- The internal H1 quotient class of a continuous 1-cocycle. -/
noncomputable def S2410InternalMk
    (z : Iut.ContinuousOneCocycle ((S2196MuActionTower p).actn n)) :
    S2204H1 p n :=
  Quotient.mk
    (Iut.continuousH1Setoid ((S2196MuActionTower p).actn n)) z
/-- The reverse quotient map: external ContH1 to the internal H1. -/
noncomputable def S2410ToInternal :
    ContH1 (LocalAbsoluteGalois p) (S2145Coeff p n) →
      S2204H1 p n :=
  Quotient.lift
    (fun c : ContH1.cocycles (LocalAbsoluteGalois p) (S2145Coeff p n) =>
      (S2410InternalMk p n (S2390OfExternalCocycle p n c)))
    (by
      intro c d hrel
      change QuotientGroup.leftRel
        (ContH1.coboundaries (G := LocalAbsoluteGalois p)
          (M := S2145Coeff p n)) c d at hrel
      rw [QuotientGroup.leftRel_apply] at hrel
      have hrel' : c * d⁻¹ ∈
          ContH1.coboundaries (LocalAbsoluteGalois p) (S2145Coeff p n) := by
        have := Subgroup.inv_mem _ hrel
        simpa [mul_inv_rev, mul_comm] using this
      have hcob : groupCohomology.IsMulCoboundary₁
          (fun g : LocalAbsoluteGalois p =>
            (S2390ToExternalCocycle p n
              (S2390OfExternalCocycle p n c)).1 g /
              (S2390ToExternalCocycle p n
                (S2390OfExternalCocycle p n d)).1 g) := by
        have hmem : groupCohomology.IsMulCoboundary₁
            (fun g => (c * d⁻¹ : ContH1.cocycles (LocalAbsoluteGalois p)
              (S2145Coeff p n)) g) :=
          (ContH1.mem_coboundaries_iff).mp hrel'
        simpa [S2390ToOf, div_eq_mul_inv] using hmem
      exact Quotient.sound
        (S2407ExternalCoboundary_to_Cohomologous p n _ _ hcob))
/-- The internal/external H^1 equivalence. -/
noncomputable def S2410H1Equiv :
    S2204H1 p n ≃
      ContH1 (LocalAbsoluteGalois p) (S2145Coeff p n) where
  toFun := S2399ToExternal p n
  invFun := S2410ToInternal p n
  left_inv x := by
    refine Quotient.inductionOn x ?_
    intro z
    let q : S2204H1 p n :=
      Quotient.mk
        (Iut.continuousH1Setoid ((S2196MuActionTower p).actn n)) z
    change S2410ToInternal p n (S2399ToExternal p n q) = q
    change S2410InternalMk p n
        (S2390OfExternalCocycle p n
          (S2390ToExternalCocycle p n z)) = q
    rw [S2390OfTo]
    rfl
  right_inv x := by
    refine Quotient.inductionOn x ?_
    intro c
    let q : ContH1 (LocalAbsoluteGalois p) (S2145Coeff p n) :=
      Quotient.mk
        (QuotientGroup.leftRel
          (ContH1.coboundaries (LocalAbsoluteGalois p)
            (S2145Coeff p n))) c
    change S2399ToExternal p n (S2410ToInternal p n q) = q
    change ContH1.mk
        (S2390ToExternalCocycle p n
          (S2390OfExternalCocycle p n c)) = q
    rw [S2390ToOf]
    rfl
/-- The comparison required by S2384, from the actual equivalence. -/
noncomputable def S2410H1Comparison :
    S2384H1Comparison p n :=
  { equiv := S2410H1Equiv p n }
/-- Finiteness of the actual level H^1, via the Kummer finite quotient. -/
theorem S2410FiniteH1 : Finite (S2204H1 p n) :=
  S2384FiniteH1OfComparison p n (S2410H1Comparison p n)
#check S2410H1Equiv
#check S2410H1Comparison
#check S2410FiniteH1
end LeanFormal.IUT.XiFPaper.S2410H1EquivDoneActual
end
