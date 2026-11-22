import tmp.sheaf.xif.paper.PaperC3RootThetaHullActual
import tmp.sheaf.xif.paper.Mzk1PhaseEquivarianceActual

/-!
# Route 3 C-Phase: a label-indexed independent mu2l phase family

This file supplies the object missing from PaperC3RootThetaHullActual:
a phase family indexed by ThetaLabel, not one diagonal synchronised phase.

* ThetaPhaseFamily assigns a unit at each label j and place v;
* phaseFamilyAction acts on the root theta value at j independently;
* synchronizedPhaseFamily is the diagonal special case where every label
  receives the same primitive-root power m;
* paperRootThetaMuOrbit is proved to be exactly the range of this diagonal
  special case.

The independent phase family is a family of units; no synchronization or
section identifying it with one global primitive root is assumed. C-Theta
equivariance for the analytic oddTheta ratio is not asserted: oddTheta has no
label/phase variable; the exact gap is documented in coord/ROUTE3-PHASE.md.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1PhaseTorsorActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.PaperC3PrimitiveMu2lRootActual
open LeanFormal.IUT.XiFPaper.PaperC3RootThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PhaseEquivarianceActual

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- A label-indexed family of mu2l phase units, independently chosen at each
label j and place v.  This is the torsor-level object; it is not a function of
one global primitive root unless a synchronization is imposed. -/
abbrev ThetaPhaseFamily : Type (max u v) :=
  (j : ThetaLabel (l := l)) -> (v : V) -> (RootExtension (G := G) v)ˣ

/-- The independent phase action on the root theta value at label j. -/
noncomputable def phaseFamilyAction
    (phase : ThetaPhaseFamily (G := G)) (j : ThetaLabel (l := l)) :
    RootThetaCarrier (G := G) :=
  fun v => phase j v * paperRootThetaUnit (G := G) (thetaLabelToSigned (l := l) j) v

/-- The diagonal, synchronized phase family: every label receives the SAME
primitive-root power m.  This is the special case represented by
paperRootThetaMuOrbit. -/
noncomputable def synchronizedPhaseFamily (m : Nat) :
    ThetaPhaseFamily (G := G) :=
  fun _j v => Units.mk0 ((primitiveMu2lRoot (G := G) v).zeta ^ m)
    (pow_ne_zero m (primitiveMu2lRoot_zeta_ne_zero (G := G) v))

/-- The synchronized family action is exactly the existing
paperRootThetaMuPoint at the corresponding signed label. -/
theorem synchronizedPhaseFamily_action
    (m : Nat) (j : ThetaLabel (l := l)) :
    phaseFamilyAction (G := G) (synchronizedPhaseFamily (G := G) m) j =
      paperRootThetaMuPoint (G := G) m (thetaLabelToSigned (l := l) j) := by
  funext v
  apply Units.ext
  simp [phaseFamilyAction, synchronizedPhaseFamily, paperRootThetaMuPoint]

/-- The existing single mu2l orbit is the range of the synchronized phase
family.  Thus it is a special case of the independent phase family, not the
general independent object. -/
theorem paperRootThetaMuOrbit_eq_range_synchronized
    (j : ThetaLabel (l := l)) :
    paperRootThetaMuOrbit (G := G) j =
      Set.range (fun m : Nat =>
        phaseFamilyAction (G := G) (synchronizedPhaseFamily (G := G) m) j) := by
  unfold paperRootThetaMuOrbit
  rw [show (fun m : Nat => phaseFamilyAction (G := G) (synchronizedPhaseFamily (G := G) m) j) =
      (fun m : Nat => paperRootThetaMuPoint (G := G) m (thetaLabelToSigned (l := l) j)) by
        funext m
        exact synchronizedPhaseFamily_action (G := G) m j]

#print axioms phaseFamilyAction
#print axioms synchronizedPhaseFamily_action
#print axioms paperRootThetaMuOrbit_eq_range_synchronized

end LeanFormal.IUT.XiFPaper.Mzk1PhaseTorsorActual
