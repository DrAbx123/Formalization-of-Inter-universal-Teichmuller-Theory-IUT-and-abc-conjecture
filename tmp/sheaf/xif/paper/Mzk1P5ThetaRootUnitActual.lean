import tmp.sheaf.xif.paper.Mzk1P5BridgeInstantiateActual

/-!
# P5-A5: actual paperRootThetaUnit = qRoot^(j^2) and reduced comparison

This file proves the actual identity

  paperRootThetaUnit j v = (twoLthRootAt v) ^ (gaussExponent j).toNat

by definition (qRoot := twoLthRootAt).  Hence the named hcomparison of
actualP5Bridge can be rewritten from paperRootThetaUnit to qRoot^(j^2); the
only remaining input is the analytic comparison itself plus c_j.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P5ThetaRootUnitActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.PaperC3RootThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1P5BridgeIntegrationActual
open LeanFormal.IUT.XiFPaper.Mzk1P5BridgeInstantiateActual
open LeanFormal.IUT.Foundations.Theta

universe u v

variable {l : PrimeGeFive}
variable {K : Type v} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type*} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
variable (v0 : V)

/-- Actual root-unit identity: paperRootThetaUnit is the qRoot power, with
qRoot := twoLthRootAt.  The unit factor is one. -/
theorem paperRootThetaUnit_eq_twoLthRootAt_pow
    (j : ThetaLabel (l := l)) :
    paperRootThetaUnit (G := G) (thetaLabelToSigned (l := l) j) v0 =
      twoLthRootAt (G := G) v0 ^
        (gaussExponent (thetaLabelToSigned (l := l) j).1).toNat := rfl

/-- Applying paperRootThetaUnit_pow_twoL to the qRoot power form. -/
theorem paperRootThetaUnit_pow_twoL_eq
    (j : ThetaLabel (l := l)) :
    (twoLthRootAt (G := G) v0 ^
        (gaussExponent (thetaLabelToSigned (l := l) j).1).toNat) ^ (2 * l.value) =
      LeanFormal.IUT.N8Closure.C3Roots.unitToAlgClosed (G.qUnit v0) ^
        (gaussExponent (thetaLabelToSigned (l := l) j).1).toNat := by
  simpa only [paperRootThetaUnit_eq_twoLthRootAt_pow (G := G) (v0 := v0) j] using
    paperRootThetaUnit_pow_twoL (G := G) (thetaLabelToSigned (l := l) j) v0

variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- The qRoot field of the instantiated bridge is the actual twoLthRootAt. -/
theorem actualP5Bridge_qRoot_eq
    (toRoot : L →+* RootExtension (G := G) v0) (r : L)
    (c : ThetaLabel (l := l) → (RootExtension (G := G) v0)ˣ)
    (m : ThetaLabel (l := l) → Nat)
    (hroot : toRoot r =
      (twoLthRootAt (G := G) v0 : RootExtension (G := G) v0) ^ l.value)
    (hcomparison : ∀ j : ThetaLabel (l := l),
      toRoot (r ^ (-(labelExp (l := l) j ^ 2))) =
        (c j : RootExtension (G := G) v0) *
          (paperPhaseUnit (G := G) (v0 := v0) m j : RootExtension (G := G) v0) *
          (paperRootThetaUnit (G := G) (thetaLabelToSigned (l := l) j) v0 :
            RootExtension (G := G) v0)) :
    (actualP5Bridge (G := G) (v0 := v0) toRoot r c m hroot hcomparison).qRoot =
      twoLthRootAt (G := G) v0 := rfl

/-- hcomparison rewritten from paperRootThetaUnit to qRoot^(j^2). -/
theorem hcomparison_qRoot_iff
    (toRoot : L →+* RootExtension (G := G) v0) (r : L)
    (c : ThetaLabel (l := l) → (RootExtension (G := G) v0)ˣ)
    (m : ThetaLabel (l := l) → Nat) :
    (∀ j : ThetaLabel (l := l),
      toRoot (r ^ (-(labelExp (l := l) j ^ 2))) =
        (c j : RootExtension (G := G) v0) *
          (paperPhaseUnit (G := G) (v0 := v0) m j : RootExtension (G := G) v0) *
          (paperRootThetaUnit (G := G) (thetaLabelToSigned (l := l) j) v0 :
            RootExtension (G := G) v0)) ↔
    (∀ j : ThetaLabel (l := l),
      toRoot (r ^ (-(labelExp (l := l) j ^ 2))) =
        (c j : RootExtension (G := G) v0) *
          (paperPhaseUnit (G := G) (v0 := v0) m j : RootExtension (G := G) v0) *
          ((twoLthRootAt (G := G) v0 ^
            (gaussExponent (thetaLabelToSigned (l := l) j).1).toNat) :
            RootExtension (G := G) v0)) := by
  simp [paperRootThetaUnit_eq_twoLthRootAt_pow (G := G) (v0 := v0)]

#print axioms paperRootThetaUnit_eq_twoLthRootAt_pow
#print axioms paperRootThetaUnit_pow_twoL_eq
#print axioms actualP5Bridge_qRoot_eq
#print axioms hcomparison_qRoot_iff

end LeanFormal.IUT.XiFPaper.Mzk1P5ThetaRootUnitActual
