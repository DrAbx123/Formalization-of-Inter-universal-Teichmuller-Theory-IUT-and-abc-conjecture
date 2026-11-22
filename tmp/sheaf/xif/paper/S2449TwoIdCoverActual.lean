import tmp.sheaf.xif.paper.S2134D9DescentActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2093D9StackActual
open LeanFormal.IUT.XiFPaper.S2029GiraudStackificationActual
open LeanFormal.IUT.XiFPaper.S2134D9DescentActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2449TwoIdCoverActual

variable {K : Type} [Field K]
variable (S : Iut.SchemeOverField K)

/-- A concrete two-copy identity cover. -/
def S2449TwoIdPresieve : Presieve S :=
  Presieve.ofArrows (fun _ : Bool => S) (fun _ => 𝟙 S)

theorem S2449TwoId_mem_self : S2449TwoIdPresieve S (𝟙 S) :=
  Presieve.ofArrows.mk true

/-- Actual effective descent for the concrete two-copy identity cover. -/
theorem S2449TwoId_effDescent :
    HasEffectiveDescentPresieve (S2029SheafPrestack K) (S2449TwoIdPresieve S) :=
  hasEffectiveDescentPresieve_of_contains_isSplitEpi
    (F := S2029SheafPrestack K) (R := S2449TwoIdPresieve S) (𝟙 S)
    (S2449TwoId_mem_self S)

/-- Every descent datum on the two-copy identity cover has an actual amalgam
(chosen classically from effective descent). -/
noncomputable def S2449Amalgam
    (D : (S2029SheafPrestack K).DescentData
      (fun (g : (S2449TwoIdPresieve S).category) => g.obj.hom)) :
    Amalgam (S2029SheafPrestack K)
      (fun (g : (S2449TwoIdPresieve S).category) => g.obj.hom) D :=
  Classical.choice
    ((hasEffectiveDescent_iff_amalgam (F := S2029SheafPrestack K) _).mp
      (S2449TwoId_effDescent S) D)

#print axioms S2449TwoId_effDescent
#print axioms S2449Amalgam

end LeanFormal.IUT.XiFPaper.S2449TwoIdCoverActual

end
