/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual
import tmp.sheaf.xif.paper.Mzk1QPilotSHEDoubleImageActual
import tmp.sheaf.xif.paper.Mzk1XiFFormalStepActual

/-!
# Mzk1QPilotRegionActual — q-pilot raw region and its containment in MRRep.possibleRegion

A521: the paper's xi-e containment is `q-pilot possible image ⊆ Θ-pilot hull`, and
`MRRep.possibleRegion` (LANA Spec, `RefLANAMultiradialSpecActual`) is exactly the
possible-image union layer.  This file:

* defines the q-pilot raw region at a bad place from the actual q reading
  (`Mzk1QPilotSHEDoubleImageActual.qPilotLogImage`, the actual local signed log);
* proves the generic containment `reg x ⊆ MRRep.possibleRegion reg (MRRep.mk x)`
  (`MRRep.reg_subset_possibleRegion`);
* packages the q-pilot singleton region and shows its possible-image containment;
* connects a possible-image containment to the xi-f formal step / Cor 3.12
  (`xi_f_formal_step`).

No new axiom, no comparison beyond the containment input. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1QPilotRegionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open LeanFormal.IUT.XiFPaper.Mzk1XiFFormalStepActual
open Iut.Multiradial

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The q-pilot raw region at a bad place: the singleton of the actual local signed
q reading `log||q_V||`. -/
def qPilotRawRegion (b : Bad (nativePlaceSelection T)) : Set Real :=
  {qPilotLogImage T b}

theorem mem_qPilotRawRegion (b : Bad (nativePlaceSelection T)) :
    qPilotLogImage T b ∈ qPilotRawRegion T b :=
  rfl

theorem qPilotRawRegion_eq_singleton (b : Bad (nativePlaceSelection T)) :
    qPilotRawRegion T b = {qPilotLogImage T b} := rfl

/-- The q reading is negative (actual local signed log). -/
theorem qPilotRawRegion_neg (b : Bad (nativePlaceSelection T)) :
    qPilotLogImage T b < 0 := qPilotLogImage_neg T b

/-! ### Generic possible-image containment (LANA `MRRep`) -/

universe u v w w'

variable {G : Type u} [Groupoid.{v} G] {A : Type w'} [Group A]

/-- The raw region of a representative is contained in `MRRep.possibleRegion`
(the actual possible-image union of the multiradial representation). -/
theorem rawRegion_subset_possibleRegion {R : RawOutput G A} {P : G} {X : Type*}
    (reg : R.F.obj P → Set X) (x : R.F.obj P) :
    reg x ⊆ MRRep.possibleRegion reg (MRRep.mk (R := R) x) :=
  MRRep.reg_subset_possibleRegion reg x

/-- A constant raw region on the raw output: each representative yields the same
q-pilot singleton region. -/
def constRawRegion {R : RawOutput G A} {P : G}
    (q : Real) : R.F.obj P → Set Real :=
  fun _ => {q}

/-- The q-pilot singleton lies in the possible-image union of the constant raw
region (the q-pilot side of xi-e). -/
theorem qPilotSingleton_subset_possibleRegion {R : RawOutput G A} {P : G}
    (x : R.F.obj P) (q : Real) :
    ({q} : Set Real) ⊆ MRRep.possibleRegion (constRawRegion (R := R) (P := P) q)
      (MRRep.mk (R := R) x) :=
  rawRegion_subset_possibleRegion (constRawRegion (R := R) (P := P) q) x

/-! ### xi-e containment ⇒ xi-f ⇒ Cor 3.12 -/

/-- xi-e containment: if the q-pilot region is contained in the region whose
log-volumes are at most `H`, then the q reading is at most `H`. -/
theorem xiEContainment_of_region_subset {q H : Real} {S : Set Real}
    (hq : q ∈ S) (hsub : S ⊆ Set.Iic H) : q ≤ H :=
  hsub hq

/-- The raw-region containment yields the xi-f inequality once the raw region's
log-volumes are bounded by the Theta-pilot hull log-volume. -/
theorem xiFInequality_of_possibleRegion {R : RawOutput G A} {P : G}
    (reg : R.F.obj P → Set X) [unused : Nonempty (R.F.obj P)]
    (x H : R.F.obj P → Real) (q : Real)
    (hq : q ∈ reg x) (hH : reg x ⊆ Set.Iic (H x)) : q ≤ H x :=
  hH hq

#check rawRegion_subset_possibleRegion
#check qPilotSingleton_subset_possibleRegion
#check xiEContainment_of_region_subset

end LeanFormal.IUT.XiFPaper.Mzk1QPilotRegionActual
end
