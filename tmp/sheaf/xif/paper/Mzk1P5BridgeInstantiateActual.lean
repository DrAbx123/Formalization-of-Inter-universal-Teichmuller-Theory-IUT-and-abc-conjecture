import tmp.sheaf.xif.paper.Mzk1P5BridgeIntegrationActual
import tmp.sheaf.xif.paper.PaperC3RootThetaHullActual

/-!
# CONDITIONAL (only c_j remains): instantiate the P5 bridge with actual root units

This file instantiates P5AnalyticRootBridge with
* thetaUnit := paperRootThetaUnit (actual root-valued paper theta);
* phase_j := primitiveMu2lRoot^m_j (actual mu2l phase);
* qRoot := twoLthRootAt (actual q_v = q^(1/2l));
and proves phase_pow and the paperRootThetaMuPoint equality by construction.

The only remaining named comparison input is c_j together with the analytic
equality hcomparison; the analytic-to-root field map toRoot and root r are still
explicit inputs.  No unconditional dictionary is claimed.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P5BridgeInstantiateActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.PaperC3PrimitiveMu2lRootActual
open LeanFormal.IUT.XiFPaper.PaperC3RootThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1P5BridgeIntegrationActual
open LeanFormal.IUT.Foundations.Theta

universe u v

variable {l : PrimeGeFive}
variable {K : Type v} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type*} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
variable (v0 : V)

/-- Local disambiguation from the Nat-valued thetaLabelExponent imported by the
root-hull dependencies; this is the Int label exponent of P5LabelShift. -/
def labelExp (j : ThetaLabel (l := l)) : Int :=
  Mzk1P5LabelShiftActual.thetaLabelExponent (l := l) j

/-- The actual synchronized mu2l phase unit primitiveMu2lRoot^m_j. -/
noncomputable def paperPhaseUnit (m : ThetaLabel (l := l) → Nat)
    (j : ThetaLabel (l := l)) : (RootExtension (G := G) v0)ˣ :=
  Units.mk0 ((primitiveMu2lRoot (G := G) v0).zeta ^ m j)
    (pow_ne_zero (m j) (primitiveMu2lRoot_zeta_ne_zero (G := G) v0))

theorem paperPhaseUnit_pow (m : ThetaLabel (l := l) → Nat)
    (j : ThetaLabel (l := l)) :
    paperPhaseUnit (G := G) (v0 := v0) m j ^ (2 * l.value) = 1 := by
  apply Units.ext
  change ((primitiveMu2lRoot (G := G) v0).zeta ^ m j) ^ (2 * l.value) = 1
  rw [← pow_mul, mul_comm (m j) (2 * l.value), pow_mul,
    (primitiveMu2lRoot (G := G) v0).zeta_pow, one_pow]

theorem paperPhaseUnit_mul_theta (m : ThetaLabel (l := l) → Nat)
    (j : ThetaLabel (l := l)) :
    (paperPhaseUnit (G := G) (v0 := v0) m j : (RootExtension (G := G) v0)ˣ) *
      paperRootThetaUnit (G := G) (thetaLabelToSigned (l := l) j) v0 =
      paperRootThetaMuPoint (G := G) (m j) (thetaLabelToSigned (l := l) j) v0 := rfl

variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- Instantiate the bridge with actual paperRootThetaUnit and primitive-root
phases.  Only c_j and the analytic comparison hcomparison remain supplied. -/
noncomputable def actualP5Bridge
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
    P5AnalyticRootBridge L (RootExtension (G := G) v0) l where
  toRoot := toRoot
  r := r
  qRoot := twoLthRootAt (G := G) v0
  root_image := hroot
  thetaUnit := fun j => paperRootThetaUnit (G := G) (thetaLabelToSigned (l := l) j) v0
  c := c
  phase := fun j => paperPhaseUnit (G := G) (v0 := v0) m j
  phase_pow := fun j => paperPhaseUnit_pow (G := G) (v0 := v0) m j
  comparison := hcomparison

theorem actualP5Bridge_thetaUnit
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
            RootExtension (G := G) v0))
    (j : ThetaLabel (l := l)) :
    (actualP5Bridge (G := G) (v0 := v0) toRoot r c m hroot hcomparison).thetaUnit j =
      paperRootThetaUnit (G := G) (thetaLabelToSigned (l := l) j) v0 := rfl

theorem actualP5Bridge_phase
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
            RootExtension (G := G) v0))
    (j : ThetaLabel (l := l)) :
    (actualP5Bridge (G := G) (v0 := v0) toRoot r c m hroot hcomparison).phase j =
      paperPhaseUnit (G := G) (v0 := v0) m j := rfl

#print axioms paperPhaseUnit_pow
#print axioms actualP5Bridge_thetaUnit
#print axioms actualP5Bridge_phase

end LeanFormal.IUT.XiFPaper.Mzk1P5BridgeInstantiateActual
