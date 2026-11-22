import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual
import tmp.sheaf.xif.paper.Mzk1SignedCor312ContractActual

/-!
# A531 audit: xi-e containment via `possibleRegion` is definitional, not Thm 3.11

Audit findings on the existing xi-e files:
* `MRRep.reg_subset_possibleRegion` (green RefLANAMultiradialSpecActual) holds for
  ANY raw region `reg`; it is the definitional property
  `reg x ⊆ ⋃_{y | mk y = mk x} reg y` of `possibleRegion`, and uses no theta values,
  no Ind1/Ind2/Ind3 possible images, and no Thm 3.11 raw output.
* `Mzk1GenuineXiEContainmentActual.qPilotConstRawRegion` is CONSTANT
  (`fun _ => qPilotRegion`), so `possibleRegion` of a constant region collapses to
  the same set and the containment is definitional.  Likewise
  `Mzk1XiEContainmentMonotoneActual` takes `qPilotContainerRegion = thetaPilotHull`.
* `Mzk1MonotoneGogopexBridgeActual.contractOfSignedContainment` uses
  `ipl := True, she := True, apt := True` with `trivial` evidence: placeholder
  qualitative fields, not IPL/SHE/APT data.

Therefore the signed comparison assembled from those containments is a
definitional identity `x <= x`, not paper Cor 3.12.  Genuine xi-e requires a
non-constant raw output (actual theta-value possible images), a separate hull
inclusion, and a strict measure increase; see
`Mzk1XiEContainmentRequirementActual` and `Mzk1GenuineXiEContainmentActual`
(the latter needs its constant-region witness replaced).

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentVacuityAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual
open CategoryTheory
open Iut.Multiradial

universe u w w'
variable {G : Type u} [Groupoid G] {A : Type w'} [Group A]

/-- Restatement of the definitional possible-image lemma: it holds for EVERY raw
region `reg`, with no Thm 3.11 input. -/
theorem any_reg_subset_possibleRegion {X : Type*} (R : RawOutput G A) {P : G}
    (reg : R.F.obj P → Set X) (x : R.F.obj P) :
    reg x ⊆ MRRep.possibleRegion (R := R) reg (MRRep.mk (R := R) x) :=
  MRRep.reg_subset_possibleRegion (R := R) reg x

/-- For a CONSTANT raw region, the possible-image union contains the constant
set trivially (same definitional lemma). -/
theorem constant_reg_subset_possibleRegion {X : Type*} (R : RawOutput G A) {P : G}
    (S : Set X) (x : R.F.obj P) :
    S ⊆ MRRep.possibleRegion (R := R) (fun _ : R.F.obj P => S) (MRRep.mk (R := R) x) :=
  any_reg_subset_possibleRegion R (fun _ => S) x

/-- A contract with `ipl := True, she := True, apt := True` is a placeholder
contract (no qualitative data). -/
noncomputable def placeholderContract
    (qSigned thetaSigned : Real) (hq : qSigned < 0) (hle : qSigned ≤ thetaSigned) :
    StepXIContract :=
  signedCor312Contract qSigned thetaSigned hq
    True trivial True trivial True trivial hle

theorem placeholderContract_ipl_is_true
    (qSigned thetaSigned : Real) (hq : qSigned < 0) (hle : qSigned ≤ thetaSigned) :
    (placeholderContract qSigned thetaSigned hq hle).ipl = True := rfl

theorem placeholderContract_she_is_true
    (qSigned thetaSigned : Real) (hq : qSigned < 0) (hle : qSigned ≤ thetaSigned) :
    (placeholderContract qSigned thetaSigned hq hle).she = True := rfl

theorem placeholderContract_apt_is_true
    (qSigned thetaSigned : Real) (hq : qSigned < 0) (hle : qSigned ≤ thetaSigned) :
    (placeholderContract qSigned thetaSigned hq hle).apt = True := rfl

end LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentVacuityAuditActual
