import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual
import tmp.sheaf.xif.paper.Mzk1XiFFormalStepActual
import tmp.sheaf.xif.paper.Mzk1MonotoneSignedDirectionActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Cor 3.12 monotone assembly: possible-image containment + log-volume monotonicity

Paper structure (IUT III, Cor 3.12, xi-e/xi-f): the q-pilot log-volume is
one of the possible Theta-pilot output log-volumes (`MRRep.possibleRegion`),
the Theta pilot is the holomorphic hull of those possible images, and
log-volume is monotone under inclusion, hence
`logVol {q} <= logVol hull = -|log Theta|`.  This file isolates exactly that
monotone step; the containment and hull inclusion are explicit named inputs. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312MonotoneAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1XiFFormalStepActual
open LeanFormal.IUT.XiFPaper.Mzk1MonotoneSignedDirectionActual
open Iut.Multiradial

universe u v w w'

variable {G : Type u} [Groupoid G] {A : Type w'} [Group A]
variable {P : G} (R : RawOutput G A)
variable (reg : R.F.obj P -> Set Real)

/-- A real-valued log-volume functional with the inclusion-monotonicity law. -/
structure MonotoneLogVolume where
  vol : Set Real -> Real
  mono : forall {S T : Set Real}, S ⊆ T -> vol S <= vol T

/-- The possible images of a representative lie in `MRRep.possibleRegion`
(green LANA lemma `reg_subset_possibleRegion`). -/
theorem mem_possibleRegion_of_representative (x : R.F.obj P) :
    reg x ⊆ MRRep.possibleRegion (R := R) reg (MRRep.mk (R := R) x) :=
  MRRep.reg_subset_possibleRegion (R := R) reg x

/-- Monotone log-volume bound: a point in the possible-image region is bounded
by the log-volume of any hull containing that region. -/
theorem logVolume_le_hull_of_containment (M : MonotoneLogVolume)
    {x : R.F.obj P} {q : Real} {hull : Set Real}
    (hq : q ∈ MRRep.possibleRegion (R := R) reg (MRRep.mk (R := R) x))
    (hHull : MRRep.possibleRegion (R := R) reg (MRRep.mk (R := R) x) ⊆ hull) :
    M.vol {q} <= M.vol hull :=
  monotone_signed_direction M.vol M.mono (Set.singleton_subset_iff.mpr (hHull hq))

/-- The StepXI contract whose q/Theta slots are the singleton q log-volume and
the hull log-volume. -/
def contractOfContainment (M : MonotoneLogVolume)
    (q hullLog : Real) (hqneg : q < 0) (hle : q <= hullLog) : StepXIContract where
  qSigned := q
  thetaSigned := hullLog
  targetSigned := hullLog
  q_negative := hqneg
  ipl := True
  she := True
  apt := True
  ipl_evidence := trivial
  she_evidence := trivial
  apt_evidence := trivial
  q_le_target := hle
  target_le_theta := le_rfl

/-- Assembly: containment + monotone hull bound + xi-f gives `Cor312Conclusion`. -/
theorem cor312_of_containment (M : MonotoneLogVolume)
    {x : R.F.obj P} {q hullLog : Real} {hull : Set Real}
    (hq : q ∈ MRRep.possibleRegion (R := R) reg (MRRep.mk (R := R) x))
    (hHull : MRRep.possibleRegion (R := R) reg (MRRep.mk (R := R) x) ⊆ hull)
    (hqLog : q = M.vol {q}) (hhullLog : hullLog = M.vol hull)
    (hqneg : q < 0) :
    Cor312Conclusion (contractOfContainment M q hullLog hqneg (by
      calc q = M.vol {q} := hqLog
        _ <= M.vol hull := logVolume_le_hull_of_containment R reg M hq hHull
        _ = hullLog := hhullLog.symm)) :=
  xi_f_formal_step (by
    show q ∈ regionLe hullLog
    calc q = M.vol {q} := hqLog
      _ <= M.vol hull := logVolume_le_hull_of_containment R reg M hq hHull
      _ = hullLog := hhullLog.symm)

end LeanFormal.IUT.XiFPaper.Mzk1Cor312MonotoneAssemblyActual

end
