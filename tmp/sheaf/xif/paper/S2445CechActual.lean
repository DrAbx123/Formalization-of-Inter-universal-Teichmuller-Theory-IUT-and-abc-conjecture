import tmp.sheaf.xif.paper.S2134D9DescentActual
import tmp.sheaf.xif.paper.S2439D9ProofActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2093D9StackActual
open LeanFormal.IUT.XiFPaper.S2029GiraudStackificationActual
open LeanFormal.IUT.XiFPaper.S2134D9DescentActual
open LeanFormal.IUT.XiFPaper.S2439D9ProofActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2445CechActual

variable {K : Type} [Field K]

/-- The Cech index category of a presieve, as the category of its arrows. -/
abbrev S2445CechNerve (S : Iut.SchemeOverField K) (R : Presieve S) : Type 1 :=
  R.category

/-- The descent data for the slice-sheaf prestack on a Cech cover. -/
abbrev S2445DescentDatum (S : Iut.SchemeOverField K) (R : Presieve S) : Type 1 :=
  (S2029SheafPrestack K).DescentData (fun (g : R.category) => g.obj.hom)

/-- The exact amalgamation requirement for a Cech cover: every descent datum has
an amalgam in the fibre at the base.  This is the precise missing construction;
no inhabitant is asserted. -/
def S2445AmalgamationRequirement (S : Iut.SchemeOverField K) (R : Presieve S) : Prop :=
  forall D : S2445DescentDatum (K := K) S R,
    Nonempty (Amalgam (S2029SheafPrestack K)
      (fun (g : R.category) => g.obj.hom) D)

/-- The full general effective-descent first missing, in amalgamation form. -/
def S2445AllCechAmalgamation : Prop :=
  forall (S : Iut.SchemeOverField K) (R : Presieve S),
    R ∈ (S2093EtalePrecoverage K).coverings S ->
      S2445AmalgamationRequirement (K := K) S R

#check S2445CechNerve
#check S2445DescentDatum
#check S2445AmalgamationRequirement
#check S2445AllCechAmalgamation
#check @Amalgam
#check @S2134EffDescentOnEtaleFamilies_iff_amalgam

theorem S2445AllCechAmalgamation_iff :
    S2134EffDescentOnEtaleFamilies (K := K) ↔ S2445AllCechAmalgamation (K := K) :=
  S2134EffDescentOnEtaleFamilies_iff_amalgam (K := K)

#print axioms S2445AllCechAmalgamation_iff

end LeanFormal.IUT.XiFPaper.S2445CechActual

end
