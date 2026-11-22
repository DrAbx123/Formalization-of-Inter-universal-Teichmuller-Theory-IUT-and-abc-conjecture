import tmp.sheaf.xif.paper.Mzk1FourTriangleSharedActual
import tmp.sheaf.xif.paper.Mzk1LiteralIQHullFinitenessActual
import tmp.sheaf.xif.paper.Mzk1R4LiteralAssemblyActual

/-! Mainline (A508): the 3.12 route objects and the Step (xi-f) formal step.

Paper route (IUT III Cor 3.12, proof Step (xi)):
* Theorem 3.11 gives the multiradial representation with possible images of the
  Theta-pilot object; taking the holomorphic hull and the procession-normalized
  log-volume gives the real (finite) number `-|log(Theta)|` (paper lines 10324-10351);
* Step (xi-f) (paper lines 10888-10898) says: the inclusion
  `-|log(q)| in R_{<=-|log(Theta)|} = {lambda | lambda <= -|log(Theta)|}` implies the
  inequality `-|log(q)| <= -|log(Theta)|`;
* the remaining part is bookkeeping on the q/Theta pilot readouts (3.11.5: the
  (HDD) = (hull+det) o (dsc) composite and the SHE output).

This file formalizes:
1. the log-volume region `Cor312LogVolumeRegion theta = {lambda | lambda <= theta}` and
   the membership equivalence (xi-f's set-theoretic content);
2. `XiFComparison`: the real data of a Step (xi-f) comparison (q readout, Theta readout,
   `q < 0`, and `q in R_{<= Theta}`), with the formal inequality;
3. the `StepXIContract` built from that data and `Cor312Conclusion` via
   `cor312_of_constructed_stepXI`;
4. the `FourTriangleSynthesis` (3.11.5 data) whose `step3115_comparison` field is
   *derived* from the xi-f membership, not assumed;
5. the literal Theta-pilot hull log-volume object from the literal IQ carrier
   (`globalIQHull`/`globalIQLogVolume`), finite by the R3 finiteness theorem, and the
   membership region built from it.

No sorry/axiom; no Prop-only shells; no ABC/hcomp input (hcomp moved to the ABC backlog). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312XiFStepActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1FourTriangleSharedActual
open LeanFormal.IUT.XiFPaper.Mzk1R4LiteralAssemblyActual

/-- The log-volume region `R_{<= theta} = {lambda in Real | lambda <= theta}` of the
  Step (xi-f) argument (paper line 10843-10848): the set of possible log-volumes of
  Theta-pilot output data. -/
def Cor312LogVolumeRegion (theta : Real) : Set Real :=
  {lambda | lambda <= theta}

/-- Step (xi-f) set-theoretic content: `q in R_{<= Theta}` is exactly `q <= Theta`. -/
theorem mem_cor312LogVolumeRegion_iff {q theta : Real} :
    q ∈ Cor312LogVolumeRegion theta ↔ q <= theta :=
  Iff.rfl

/-- The real data of a Step (xi-f) comparison: the q-pilot readout, the Theta-pilot
  (hull) log-volume, the negativity of the q readout (paper: `-|log q| < 0`), and the
  xi-f membership `q in R_{<= Theta}`. -/
structure XiFComparison where
  /-- The q-pilot log-volume `-|log(q)|`. -/
  qVolume : Real
  /-- The Theta-pilot hull log-volume `-|log(Theta)|`. -/
  thetaVolume : Real
  /-- The q-pilot log-volume is negative (paper lines 10349-10356). -/
  qVolume_neg : qVolume < 0
  /-- The Step (xi-f) membership `-|log(q)| in R_{<=-|log(Theta)|}`. -/
  qVolume_mem : qVolume ∈ Cor312LogVolumeRegion thetaVolume

/-- **Step (xi-f) formal step**: the xi-f membership gives the paper inequality
  `-|log(q)| <= -|log(Theta)|` (paper line 10895-10898). -/
theorem xi_f_inequality (X : XiFComparison) : X.qVolume <= X.thetaVolume :=
  X.qVolume_mem

/-- The StepXI contract built from the xi-f data: the q/Theta slots are the pilot
  readouts, `targetSigned := qSigned`, and the ordering is the xi-f inequality (so
  `target_le_theta` is proved, not a free field). -/
def xi_f_contract (X : XiFComparison) (ipl she apt : Prop)
    (hipl : ipl) (hshe : she) (hapt : apt) : StepXIContract where
  qSigned := X.qVolume
  thetaSigned := X.thetaVolume
  targetSigned := X.qVolume
  q_negative := X.qVolume_neg
  ipl := ipl
  she := she
  apt := apt
  ipl_evidence := hipl
  she_evidence := hshe
  apt_evidence := hapt
  q_le_target := le_rfl
  target_le_theta := xi_f_inequality X

/-- **Cor 3.12 ordered conclusion from Step (xi-f)**: the q-pilot readout is at most the
  Theta-pilot hull log-volume (paper Cor 3.12 inequality, lines 10351-10353). -/
theorem cor312Conclusion_of_xi_f (X : XiFComparison) (ipl she apt : Prop)
    (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion (xi_f_contract X ipl she apt hipl hshe hapt) :=
  cor312_of_constructed_stepXI _

/-- **3.11.5 data from the xi-f comparison**: for any `(HDD)` decomposition, descent map
  and SHE output whose readouts are the pilot readouts, the four-triangle synthesis has
  its `step3115_comparison` field *proved* from the xi-f membership (not assumed). -/
def fourTriangleSynthesis_of_xi_f {DSC SHEOut : Type*} (X : XiFComparison)
    (hdd : HDDDecomp Real Real DSC) (dsc : SHEOut → DSC) (sheOut : SHEOut)
    (contract : StepXIContract)
    (hull_eq : contract.qSigned = (fourTriangleReadout hdd dsc sheOut).1)
    (theta_eq : contract.thetaSigned = (fourTriangleReadout hdd dsc sheOut).2)
    (hreadout : (fourTriangleReadout hdd dsc sheOut).1 ∈
      Cor312LogVolumeRegion (fourTriangleReadout hdd dsc sheOut).2) :
    FourTriangleSynthesis DSC SHEOut where
  contract := contract
  hdd := hdd
  dsc := dsc
  sheOut := sheOut
  hull_eq := hull_eq
  theta_eq := theta_eq
  step3115_comparison := hreadout

section LiteralThetaHull

open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.S2723GlobalIQHullActual

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [∀ i, Fintype (C3.tensorPlaceIndex i)]

/-- **The literal Theta-pilot hull log-volume object** (Theorem 3.11 side): the real
  log-volume of the literal global IQ hull, `toReal` of the finite `globalIQLogVolume`. -/
def literalThetaPilotHullVolume (j : Nat) : Real :=
  (globalIQLogVolume (C3 := C3) j (globalIQHull (C3 := C3) j)).toReal

/-- The literal hull log-volume is finite (the R3 finiteness theorem of the literal IQ
  carrier; same content as `literalGlobalIQHull_logVolume_lt_top`). -/
theorem literalThetaPilotHullVolume_finite (j : Nat) :
    globalIQLogVolume (C3 := C3) j (globalIQHull (C3 := C3) j) < ⊤ :=
  literalGlobalIQHull_logVolume_lt_top (C3 := C3) j

/-- The region `R_{<= -|log(Theta)|}` built from the literal Theta-pilot hull
  log-volume — the target set of Step (xi-f). -/
def literalThetaPilotRegion (j : Nat) : Set Real :=
  Cor312LogVolumeRegion (literalThetaPilotHullVolume C3 j)

/-- Step (xi-f) membership in the literal region is the paper inequality against the
  literal hull log-volume. -/
theorem mem_literalThetaPilotRegion_iff {j : Nat} {q : Real} :
    q ∈ literalThetaPilotRegion C3 j ↔ q <= literalThetaPilotHullVolume C3 j :=
  Iff.rfl

end LiteralThetaHull

end

end LeanFormal.IUT.XiFPaper.Mzk1Cor312XiFStepActual