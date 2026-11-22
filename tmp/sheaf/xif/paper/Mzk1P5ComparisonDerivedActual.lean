import tmp.sheaf.xif.paper.Mzk1P5HunitDerivedActual

/-!
# comparison as theorem: canonical c_j from phase and root

In the instantiate bridge, root_image gives
toRoot(r^(-n)) = qRoot^(-(l*n)), and paperRootThetaUnit_j = qRoot^n.
Thus the comparison has the canonical witness

  c_j := phase_j^(-1) * qRoot^(-((l+1)*n))

and hcomparison is no longer a named input.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P5ComparisonDerivedActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
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

/-- paperRootThetaUnit is qRoot^(j^2), as units. -/
theorem paperRootThetaUnit_eq_qRoot_zpow
    (j : ThetaLabel (l := l)) :
    paperRootThetaUnit (G := G) (thetaLabelToSigned (l := l) j) v0 =
      twoLthRootAt (G := G) v0 ^
        (Mzk1P5LabelShiftActual.thetaLabelExponent (l := l) j ^ 2) := by
  apply Units.ext
  rw [paperRootThetaUnit_eq_twoLthRootAt_pow (G := G) (v0 := v0) j]
  have hnonneg : 0 ≤ (thetaLabelToSigned (l := l) j).1 ^ 2 := sq_nonneg _
  rw [show Mzk1P5LabelShiftActual.thetaLabelExponent (l := l) j ^ 2 =
      ((gaussExponent (thetaLabelToSigned (l := l) j).1).toNat : Int) by
    simp [Mzk1P5LabelShiftActual.thetaLabelExponent, gaussExponent,
      Int.toNat_of_nonneg hnonneg]]
  rw [zpow_natCast]

/-- root_image lifted to integral powers, directly from hroot. -/
theorem toRoot_zpow
    (toRoot : L →+* RootExtension (G := G) v0) (r : L)
    (hroot : toRoot r =
      (twoLthRootAt (G := G) v0 : RootExtension (G := G) v0) ^ l.value)
    (N : Int) :
    toRoot (r ^ N) =
      (twoLthRootAt (G := G) v0 : RootExtension (G := G) v0) ^
        ((l.value : Int) * N) := by
  rw [map_zpow₀, hroot]
  have hcast : ((twoLthRootAt (G := G) v0 : RootExtension (G := G) v0) ^ l.value) =
      ((twoLthRootAt (G := G) v0 : RootExtension (G := G) v0) ^ (l.value : Int)) :=
    (zpow_natCast (twoLthRootAt (G := G) v0 : RootExtension (G := G) v0) l.value).symm
  rw [hcast, ← zpow_mul]

/-- The canonical c_j from phase and root. -/
noncomputable def cOfPhase (m : ThetaLabel (l := l) → Nat)
    (j : ThetaLabel (l := l)) : (RootExtension (G := G) v0)ˣ :=
  (paperPhaseUnit (G := G) (v0 := v0) m j)⁻¹ *
    (twoLthRootAt (G := G) v0) ^
      (-(((l.value : Int) + 1) *
        Mzk1P5LabelShiftActual.thetaLabelExponent (l := l) j ^ 2))


/-- The comparison holds with the canonical cOfPhase; hcomparison is a theorem. -/
theorem comparison_cOfPhase
    (toRoot : L →+* RootExtension (G := G) v0) (r : L)
    (hroot : toRoot r =
      (twoLthRootAt (G := G) v0 : RootExtension (G := G) v0) ^ l.value)
    (m : ThetaLabel (l := l) → Nat) (j : ThetaLabel (l := l)) :
    toRoot (r ^ (-(Mzk1P5LabelShiftActual.thetaLabelExponent (l := l) j ^ 2))) =
      (cOfPhase (G := G) (v0 := v0) m j : RootExtension (G := G) v0) *
        (paperPhaseUnit (G := G) (v0 := v0) m j : RootExtension (G := G) v0) *
        (paperRootThetaUnit (G := G) (thetaLabelToSigned (l := l) j) v0 :
          RootExtension (G := G) v0) := by
  rw [toRoot_zpow (G := G) (v0 := v0) toRoot r hroot (-(Mzk1P5LabelShiftActual.thetaLabelExponent (l := l) j ^ 2))]
  have hc : (cOfPhase (G := G) (v0 := v0) m j : RootExtension (G := G) v0) =
      (paperPhaseUnit (G := G) (v0 := v0) m j : RootExtension (G := G) v0)⁻¹ *
        (twoLthRootAt (G := G) v0 : RootExtension (G := G) v0) ^
          (-(((l.value : Int) + 1) *
            Mzk1P5LabelShiftActual.thetaLabelExponent (l := l) j ^ 2)) := by
    simp [cOfPhase]
  rw [hc, paperRootThetaUnit_eq_qRoot_zpow (G := G) (v0 := v0) j]
  have hp0 : (paperPhaseUnit (G := G) (v0 := v0) m j : RootExtension (G := G) v0) ≠ 0 :=
    Units.ne_zero _
  have hq0 : (twoLthRootAt (G := G) v0 : RootExtension (G := G) v0) ≠ 0 := Units.ne_zero _
  field_simp [hp0, hq0]
  rw [Units.val_zpow_eq_zpow_val]
  rw [← zpow_add₀ hq0]
  congr 1
  ring

#print axioms comparison_cOfPhase

#print axioms paperRootThetaUnit_eq_qRoot_zpow
#print axioms toRoot_zpow

end LeanFormal.IUT.XiFPaper.Mzk1P5ComparisonDerivedActual
