import tmp.sheaf.xif.PaperSignedHull
import tmp.sheaf.n8.closure.C9IUTBridgeOutput

/-! # S2362: fixed-C 3.12 readout from U2K2 to PaperSignedHull

The fixed-C mainline needs an actual output `D` in the restricted output family
`P_C` whose signed readout `nu_C(D)` equals (or epsilon-approximates) the
q-pilot value `Q_C`.  The C9 notes show `U2K2` transports the q-mark but does not
produce that output-family membership or readout.  This file isolates the
exact missing projection and proves the scalar step once it is supplied:
`Q_C ≤ signedHullLogVolume` from the xi-f inequality, with the hull volume
finite from `PaperSignedHull.ambient_hull_logVolume_lt_top`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2362MainlineReadoutActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.N8Closure.C9IUTBridgeOutput

universe u v uo

variable {X : Type u} {label : Type v} [Fintype label]

/-- Fixed-C data: the q-pilot value is a real number with the xi-f hull
inequality as an explicit premise (not a construction of the output). -/
structure S2362FixedCData (P : PaperSignedHull X label) where
  qPilotLogVolume : Real
  qPilotLogVolume_eq_neg_abs : Prop
  xi_f_inequality : qPilotLogVolume ≤ P.signedHullLogVolume

/-- An actual output readout: the output `D` lies in the restricted family
`P_C` and `nu_C(D) = Q_C`, where `Q_C` is the q-pilot value. -/
structure S2362ActualOutputReadout
    (P : PaperSignedHull X label)
    (F : S2362FixedCData P) where
  Output : Type uo
  P_C : Set Output
  nu_C : Output → Real
  Q_C : Real
  Q_C_eq_qPilot : Q_C = F.qPilotLogVolume
  D : Output
  D_mem : D ∈ P_C
  readout_eq : nu_C D = Q_C

/-- The scalar step: an actual output readout gives `Q_C ≤ signedHullLogVolume`,
and the ambient hull log-volume is finite. -/
theorem s2362_qPilot_le_hull
    {P : PaperSignedHull X label}
    {F : S2362FixedCData P}
    (R : S2362ActualOutputReadout P F) :
    R.Q_C ≤ P.signedHullLogVolume :=
  R.Q_C_eq_qPilot.trans_le F.xi_f_inequality

theorem s2362_hull_logVolume_lt_top
    (P : PaperSignedHull X label) :
    P.ambient.logVolume P.ambient.hull < ⊤ :=
  P.ambient_hull_logVolume_lt_top

/-- Exact missing C1/xi-f projection: an output-family member with the required
readout equality. -/
structure S2362C1OutputReadoutProjectionRequired
    (P : PaperSignedHull X label)
    (F : S2362FixedCData P) where
  Output : Type uo
  P_C : Set Output
  nu_C : Output → Real
  Q_C : Real
  Q_C_eq_qPilot : Q_C = F.qPilotLogVolume
  exists_output : ∃ D : Output, D ∈ P_C ∧ nu_C D = Q_C

/-- Given the exact missing projection, construct the actual readout by choice. -/
noncomputable def s2362ReadoutOfProjection
    {P : PaperSignedHull X label}
    {F : S2362FixedCData P}
    (C : S2362C1OutputReadoutProjectionRequired P F) :
    S2362ActualOutputReadout P F := by
  classical
  let D := Classical.choose C.exists_output
  have hspec := Classical.choose_spec C.exists_output
  exact
    { Output := C.Output
      P_C := C.P_C
      nu_C := C.nu_C
      Q_C := C.Q_C
      Q_C_eq_qPilot := C.Q_C_eq_qPilot
      D := D
      D_mem := hspec.1
      readout_eq := hspec.2 }

/-- The U2K2-to-`P_C` interface gap: the transported q-mark must produce an
actual output in the restricted family, plus its signed readout equality.  No
inhabitant is asserted. -/
structure S2362U2K2ToPCRequired
    (P : PaperSignedHull X label)
    (F : S2362FixedCData P) where
  Output : Type uo
  P_C : Set Output
  nu_C : Output → Real
  Q_C : Real
  Q_C_eq_qPilot : Q_C = F.qPilotLogVolume
  U2K2_mark_mem : Prop
  readout_projection : Prop

/-- Mainline scalar conclusion from the actual output readout: Q_C ≤ H_C and
H_C is finite. -/
theorem s2362_mainline_scalar
    {P : PaperSignedHull X label}
    {F : S2362FixedCData P}
    (R : S2362ActualOutputReadout P F) :
    R.Q_C ≤ P.signedHullLogVolume ∧
      P.ambient.logVolume P.ambient.hull < ⊤ :=
  ⟨s2362_qPilot_le_hull R, s2362_hull_logVolume_lt_top P⟩

/-- The same conclusion from the exact missing C1 projection. -/
theorem s2362_mainline_scalar_of_projection
    {P : PaperSignedHull X label}
    {F : S2362FixedCData P}
    (C : S2362C1OutputReadoutProjectionRequired P F) :
    (s2362ReadoutOfProjection C).Q_C ≤ P.signedHullLogVolume ∧
      P.ambient.logVolume P.ambient.hull < ⊤ :=
  s2362_mainline_scalar (s2362ReadoutOfProjection C)

#check s2362_mainline_scalar
#check s2362_mainline_scalar_of_projection
#check s2362_qPilot_le_hull
#check s2362_hull_logVolume_lt_top
#check S2362C1OutputReadoutProjectionRequired
#check s2362ReadoutOfProjection
#check S2362U2K2ToPCRequired

end LeanFormal.IUT.XiFPaper.S2362MainlineReadoutActual
end
