import tmp.sheaf.xif.paper.Mzk1IUTIVSection2EquivActual
import tmp.sheaf.xif.paper.S3135EndToEndAssemblyActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1IUTIVSection2RouteAssemblyActual — §2 uniformity route assembled

Assembles the proved §2 uniformity/display-family equivalence with the EXIT0
section-2 end-to-end assembly: the §2 uniformity input yields ABCConjecture.
This is the constructible part of the §2 rung; the uniformity input itself
remains the named analytic input.  No closure claim; gate NOT PASSED;
registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIVSection2RouteAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3135IUTIVThetaBoundToComparisonActual
open LeanFormal.IUT.XiFPaper.S3135ComparisonAssemblyActual
open LeanFormal.IUT.XiFPaper.S3135EndToEndAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVSection2EquivActual

theorem ABCHeightWeightAdditiveBoundV2_of_section2Uniformity
    (hu : IUTIVSection2Uniformity) : ABCHeightWeightAdditiveBoundV2 :=
  s3135_ABCHeightWeightAdditiveBoundV2_of_paperInputs hu

theorem abcConjecture_of_displayFamily (hf : IUTIVSection2UniformDisplayFamily) :
    ABCConjecture :=
  s3135_abcConjecture_of_section2DisplayFamily hf

theorem abcConjecture_of_section2Uniformity (hu : IUTIVSection2Uniformity) :
    ABCConjecture :=
  s3135_abcConjecture_of_section2DisplayFamily
    ((uniformity_iff_displayFamily).mp hu)

end LeanFormal.IUT.XiFPaper.Mzk1IUTIVSection2RouteAssemblyActual

end
