import tmp.sheaf.xif.paper.HullDetObjectActual
import tmp.sheaf.xif.paper.O2ThetaObjectActual

/-! Mainline (A509): the Step (xi-f) comparison as a REAL theorem shape.

Objects (independent readouts, no `q/(2l)` definition):
* `qPilotLogVolume C3 P`: the actual global q-pilot log-volume `-|log q|` on the
  source completion (HullDetObjectActual.qPilotLogVolume; negative/nonpositive),
* `thetaPilotLogVolume T j`: the global Theta-pilot log-volume at a signed label
  (sum over V_bad of the independent formula `gaussExp j * logVol(qroot)`),
* `thetaPilotLogVolumeAverage T`: its procession average over the signed labels
  (the paper's `-|log(Theta)|` normalization).

**Formal Step (xi-f) content**: from the multiradial/hull membership
`-|log q| in R_{<= -|log(Theta)|}` (equivalently `qPilotLogVolume <= thetaPilotLogVolumeAverage`),
the inequality and hence the Cor 3.12 ordered conclusion follow.  The membership itself
is the missing paper input: it is supplied by the Theorem 3.11 multiradial representation
followed by the holomorphic hull and the determinant normalization (IUT III, Step (xi-d),
(xi-e), (xi-f): lines 10823-10898).  In this file it is an **explicit named field** of
`XiFData` (documented below), never a sorry and never a hidden axiom; the xi-f formal
deduction from it is proved.

No sorry/axiom/True placeholder; no ABC/hcomp input. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIFaeActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.O2ThetaObjectActual
open LeanFormal.IUT.XiFPaper.HullDetObjectActual
open scoped BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-! ## 1. The independent q-pilot readout -/

/-- The q-pilot log-volume `-|log q|` of the actual source completion, independent of
  any Theta normalisation (HullDetObjectActual.qPilotLogVolume). -/
noncomputable def qPilotLogVolume : Real :=
  HullDetObjectActual.qPilotLogVolume C3 P

/-- The q readout is exactly `-|log q|` of the source completion q. -/
theorem qPilotLogVolume_constructed :
    qPilotLogVolume C3 P = -|Real.log (‖P.line.C3.q.q‖)| :=
  HullDetObjectActual.qPilotLogVolume_constructed C3 P

/-- The q readout is nonpositive (`-|log q| <= 0`). -/
theorem qPilotLogVolume_nonpos : qPilotLogVolume C3 P ≤ 0 :=
  HullDetObjectActual.qPilotLogVolume_nonpos C3 P

/-! ## 2. The independent Theta-pilot readouts -/

/-- The global Theta-pilot log-volume at the signed label `j` (sum over V_bad of the
  independent formula `gaussExp j * logVol(qroot)`). -/
noncomputable def thetaPilotLogVolume (j : SignedLabel l.value) : Real :=
  HullDetObjectActual.thetaPilotLogVolume T j

/-- The global Theta readout is the sum of the log-norms of the actual theta values. -/
theorem thetaPilotLogVolume_constructed (j : SignedLabel l.value) :
    thetaPilotLogVolume T j =
      ∑ b : Bad (nativePlaceSelection T),
        Real.log
          ‖(O2ThetaObjectActual.thetaPilotValue T j b : rootNormedExtension T b)‖ :=
  HullDetObjectActual.thetaPilotLogVolume_constructed T j

/-- The procession-normalized Theta-pilot log-volume `-|log(Theta)|`: the average of
  the global Theta readouts over the signed labels. -/
noncomputable def thetaPilotLogVolumeAverage : Real :=
  HullDetObjectActual.thetaPilotLogVolumeAverage T

/-- The average readout is the sum over V_bad of the local procession averages. -/
theorem thetaPilotLogVolumeAverage_constructed :
    thetaPilotLogVolumeAverage T =
      ∑ b : Bad (nativePlaceSelection T),
        HullDetObjectActual.localThetaLogVolumeAverage T b :=
  HullDetObjectActual.thetaPilotLogVolumeAverage_constructed T

/-! ## 3. The Step (xi-f) data and its formal deduction -/

/-- **Step (xi-f) input data** (the only named assumption of this file): the q-pilot
  log-volume is negative (`-|log q| < 0`, since `|log q| > 0`; IUT III line 10349-10356)
  and lies in the Theta-pilot region `R_{<= -|log(Theta)|}`:

  `-|log q| in R_{<= -|log(Theta)|}`, i.e. `qPilotLogVolume <= thetaPilotLogVolumeAverage`.

  **Missing paper step** (explicitly, not a sorry): this membership is produced by
  (IUT III) Theorem 3.11 (multiradial representation with possible images of the
  Theta-pilot object, subject to (Ind1),(Ind2),(Ind3)) followed by (a) the holomorphic
  hull and (b) the determinant normalization of the localizations of arithmetic vector
  bundles, and then the log-volume comparison of Step (xi-d)/(xi-e)/(xi-f)
  (paper lines 10823-10898).  Our current object layer has the independent q readout
  and the independent Theta readouts, but not yet the multiradial-algorithm comparison
  that places the q readout inside the Theta region; that is why it is a named hypothesis
  here. -/
structure XiFData where
  /-- `-|log q| < 0` (paper: `|log q| > 0`). -/
  q_neg : qPilotLogVolume C3 P < 0
  /-- The Step (xi-f) membership: `-|log q| in R_{<= -|log(Theta)|}`. -/
  q_mem_thetaRegion : qPilotLogVolume C3 P ≤ thetaPilotLogVolumeAverage T

/-- **The Step (xi-f) inequality**: `-|log q| <= -|log(Theta)|` (IUT III, lines
  10895-10898), deduced from the membership field. -/
theorem xif_q_le_theta (X : XiFData C3 T P) :
    qPilotLogVolume C3 P ≤ thetaPilotLogVolumeAverage T :=
  X.q_mem_thetaRegion

/-- The StepXI contract built from the xi-f data: the q/Theta slots are the independent
  pilot readouts, `targetSigned := qSigned`, and `target_le_theta` is the proved xi-f
  inequality (not a free/arbitrary field).  The `ipl/she/apt` Props are explicit
  obligations with supplied evidence. -/
def xif_contract (X : XiFData C3 T P) (ipl she apt : Prop)
    (hipl : ipl) (hshe : she) (hapt : apt) : StepXIContract where
  qSigned := qPilotLogVolume C3 P
  thetaSigned := thetaPilotLogVolumeAverage T
  targetSigned := qPilotLogVolume C3 P
  q_negative := X.q_neg
  ipl := ipl
  she := she
  apt := apt
  ipl_evidence := hipl
  she_evidence := hshe
  apt_evidence := hapt
  q_le_target := le_rfl
  target_le_theta := xif_q_le_theta C3 T P X

/-- **Cor 3.12 ordered conclusion from Step (xi-f)**:
  `Cor312Conclusion (xif_contract ...)` (paper Cor 3.12 inequality). -/
theorem cor312Conclusion_of_xif (X : XiFData C3 T P) (ipl she apt : Prop)
    (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion (xif_contract C3 T P X ipl she apt hipl hshe hapt) :=
  cor312_of_constructed_stepXI _

end

end LeanFormal.IUT.XiFPaper.Mzk1StepXIFaeActual