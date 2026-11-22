import tmp.sheaf.xif.paper.S2448GeneralCoverActual
import tmp.sheaf.xif.paper.S2445CechActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2448GeneralCoverActual
open LeanFormal.IUT.XiFPaper.S2093D9StackActual
open LeanFormal.IUT.XiFPaper.S2029GiraudStackificationActual
open LeanFormal.IUT.XiFPaper.S2134D9DescentActual
open LeanFormal.IUT.XiFPaper.S2445CechActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2453NonSplitCanonicalAmalgamActual

/-- Canonical descent datum of an object M on the concrete non-split cover. -/
abbrev S2453CanonicalDatum
    (M : (S2029SheafPrestack K).obj (.mk (Opposite.op baseScheme))) :
    (S2029SheafPrestack K).DescentData
      (fun (g : coverPresieve.category) => g.obj.hom) :=
  (S2029SheafPrestack K).toDescentData
    (fun (g : coverPresieve.category) => g.obj.hom) |>.obj M

/-- Actual canonical amalgam on the concrete non-split cover. -/
noncomputable def S2453CanonicalAmalgam
    (M : (S2029SheafPrestack K).obj (.mk (Opposite.op baseScheme))) :
    Amalgam (S2029SheafPrestack K)
      (fun (g : coverPresieve.category) => g.obj.hom)
      (S2453CanonicalDatum M) where
  M := M
  iso := Iso.refl _

/-- Nonempty form. -/
theorem S2453CanonicalNonempty
    (M : (S2029SheafPrestack K).obj (.mk (Opposite.op baseScheme))) :
    Nonempty (Amalgam (S2029SheafPrestack K)
      (fun (g : coverPresieve.category) => g.obj.hom)
      (S2453CanonicalDatum M)) :=
  ⟨S2453CanonicalAmalgam M⟩

#print axioms S2453CanonicalAmalgam
#print axioms S2453CanonicalNonempty

end LeanFormal.IUT.XiFPaper.S2453NonSplitCanonicalAmalgamActual

end
