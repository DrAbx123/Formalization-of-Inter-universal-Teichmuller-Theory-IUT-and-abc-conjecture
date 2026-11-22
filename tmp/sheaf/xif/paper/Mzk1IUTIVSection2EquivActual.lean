import tmp.sheaf.xif.paper.S3135IUTIVThetaBoundToComparisonActual
import tmp.sheaf.xif.paper.S3135ComparisonAssemblyActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1IUTIVSection2EquivActual — equivalence of the two §2 uniformity inputs

Genuine new equivalence: the IUT IV §2 uniformity input and the section-2
uniform display family are equivalent (the dictionary readout is supplied by
the arithmetic weight in one direction, and forgotten in the other).
No new paper input is proved; named inputs remain named; no closure;
gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIVSection2EquivActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3135IUTIVThetaBoundToComparisonActual
open LeanFormal.IUT.XiFPaper.S3135ComparisonAssemblyActual

theorem displayFamily_of_uniformity (hu : IUTIVSection2Uniformity) :
    IUTIVSection2UniformDisplayFamily := by
  intro eps heps
  obtain ⟨l, dmod, emod, eta, D, W, hl, hd, he, heta, hslope, hconst, hdict, hdisp⟩ :=
    hu eps heps
  refine ⟨l, dmod, emod, eta, D, hl, hd, he, heta, hslope, hconst, ?_⟩
  intro a b c habc
  have h := hdisp a b c habc
  rw [hdict a b c habc] at h
  exact h

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
    simpa [S3135ComparisonAssemblyActual.freyLogQ,
      S3135IUTIVThetaBoundToComparisonActual.freyLogQ] using hdisp a b c habc

theorem uniformity_iff_displayFamily :
    IUTIVSection2Uniformity ↔ IUTIVSection2UniformDisplayFamily :=
  ⟨displayFamily_of_uniformity, uniformity_of_displayFamily⟩

end LeanFormal.IUT.XiFPaper.Mzk1IUTIVSection2EquivActual

end
