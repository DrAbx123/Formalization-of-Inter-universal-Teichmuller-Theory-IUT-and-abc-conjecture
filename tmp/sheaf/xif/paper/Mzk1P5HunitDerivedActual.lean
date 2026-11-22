import tmp.sheaf.xif.paper.Mzk1P5PhaseDerivedActual
import tmp.sheaf.xif.paper.Mzk1P5ThetaRootUnitActual

/-!
# hunit derived in the instantiate bridge

In actualP5Bridge, thetaUnit is paperRootThetaUnit and qRoot is twoLthRootAt.
The A5 identity paperRootThetaUnit = twoLthRootAt^(j^2) then gives hunit
without an extra hypothesis:

  (actualP5Bridge ...).thetaUnit j = ((actualP5Bridge ...).qRoot)^(j^2).

This removes hunit from the final phase_relation/CJ consumers.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P5HunitDerivedActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.PaperC3RootThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1P5LabelShiftActual
open LeanFormal.IUT.XiFPaper.Mzk1P5BridgeIntegrationActual
open LeanFormal.IUT.XiFPaper.Mzk1P5BridgeInstantiateActual
open LeanFormal.IUT.XiFPaper.Mzk1P5ThetaRootUnitActual
open LeanFormal.IUT.Foundations.Theta

universe u v

variable {l : PrimeGeFive}
variable {K : Type v} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type*} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
variable (v0 : V)
variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

variable (toRoot : L →+* RootExtension (G := G) v0) (r : L)
variable (c : ThetaLabel (l := l) → (RootExtension (G := G) v0)ˣ)
variable (m : ThetaLabel (l := l) → Nat)
variable (hroot : toRoot r =
  (twoLthRootAt (G := G) v0 : RootExtension (G := G) v0) ^ l.value)
variable (hcomparison : ∀ j : ThetaLabel (l := l),
  toRoot (r ^ (-(labelExp (l := l) j ^ 2))) =
    (c j : RootExtension (G := G) v0) *
      (paperPhaseUnit (G := G) (v0 := v0) m j : RootExtension (G := G) v0) *
      (paperRootThetaUnit (G := G) (thetaLabelToSigned (l := l) j) v0 :
        RootExtension (G := G) v0))

theorem actualP5Bridge_hunit (j : ThetaLabel (l := l)) :
    (actualP5Bridge (G := G) (v0 := v0) toRoot r c m hroot hcomparison).thetaUnit j =
      ((actualP5Bridge (G := G) (v0 := v0) toRoot r c m hroot hcomparison).qRoot :
          RootExtension (G := G) v0) ^
        (Mzk1P5LabelShiftActual.thetaLabelExponent (l := l) j ^ 2) := by
  rw [actualP5Bridge_thetaUnit (G := G) (v0 := v0) toRoot r c m hroot hcomparison j,
    actualP5Bridge_qRoot_eq (G := G) (v0 := v0) toRoot r c m hroot hcomparison]
  rw [paperRootThetaUnit_eq_twoLthRootAt_pow (G := G) (v0 := v0) j]
  have hnonneg : 0 ≤ (thetaLabelToSigned (l := l) j).1 ^ 2 := sq_nonneg _
  rw [show Mzk1P5LabelShiftActual.thetaLabelExponent (l := l) j ^ 2 =
      ((gaussExponent (thetaLabelToSigned (l := l) j).1).toNat : Int) by
    simp [Mzk1P5LabelShiftActual.thetaLabelExponent, gaussExponent,
      Int.toNat_of_nonneg hnonneg]]
  rw [zpow_natCast, Units.val_pow_eq_pow_val]

#print axioms actualP5Bridge_hunit

end LeanFormal.IUT.XiFPaper.Mzk1P5HunitDerivedActual
