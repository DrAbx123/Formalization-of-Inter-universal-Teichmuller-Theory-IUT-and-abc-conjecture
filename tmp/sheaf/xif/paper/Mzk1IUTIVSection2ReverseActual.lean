import tmp.sheaf.xif.paper.S3135IUTIVThetaBoundToComparisonActual
import tmp.sheaf.xif.paper.S3135ComparisonAssemblyActual
import tmp.sheaf.xif.paper.S3135EndToEndAssemblyActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1IUTIVSection2ReverseActual — §2 display family ⇒ uniformity and ABC

Genuine new consumers for the IUT IV §1→§2 passage:
* the section-2 uniform display family yields the section-2 uniformity input
  (taking the dictionary readout W to be the arithmetic weight);
* hence ABCConjecture via the EXIT0 end-to-end assembly.
No new paper input is proved; named inputs remain named; no closure;
gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIVSection2ReverseActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3135IUTIVThetaBoundToComparisonActual
open LeanFormal.IUT.XiFPaper.S3135ComparisonAssemblyActual
open LeanFormal.IUT.XiFPaper.S3135EndToEndAssemblyActual

/-- The section-2 uniform display family yields the §2 uniformity input. -/
theorem uniformity_of_displayFamily (hf : IUTIVSection2UniformDisplayFamily) :
    IUTIVSection2Uniformity := by
  intro eps heps
  obtain ⟨l, dmod, emod, eta, D, hl, hd, he, heta, hslope, hconst, hdisp⟩ :=
    hf eps heps
  refine ⟨l, dmod, emod, eta, D, (fun a b c => arithmeticWeight (abcRationalPoint a c)),
    hl, hd, he, heta, hslope, hconst, ?_, ?_⟩
  · intro a b c _
    rfl
  · intro a b c habc
    exact hdisp a b c habc

/-- ABCConjecture from the section-2 uniform display family. -/
theorem abcConjecture_of_displayFamily (hf : IUTIVSection2UniformDisplayFamily) :
    ABCConjecture :=
  s3135_abcConjecture_of_section2DisplayFamily hf

end LeanFormal.IUT.XiFPaper.Mzk1IUTIVSection2ReverseActual

end
