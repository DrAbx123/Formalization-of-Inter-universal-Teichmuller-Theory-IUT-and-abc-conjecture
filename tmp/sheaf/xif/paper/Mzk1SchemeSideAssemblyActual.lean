import LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary

/-!
# Mzk1SchemeSideAssemblyActual — real assembly: Definition 3.1 scheme-side package

Status: PENDING-VERIFY. No sorry, no axiom.
Consumer (not adapted copy): assembles the compiled Definition 3.1 source contract
projections (bijective sectionMap, finite/infinite place data, positive cusp epsilon)
into one scheme-side rung package. Uses only proved theorems of
SourceDefinition31Boundary. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1SchemeSideAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

universe u v w

/-- Genuine assembly theorem: Definition 3.1 scheme-side data package. -/
theorem sourceDefinition31_scheme_side_assembly {l : PrimeGeFive}
    (S : SourceDefinition31Data l) :
    Function.Bijective S.sections.sectionMap ∧
      S.sections.finitePlaceData ∧ S.sections.infinitePlaceData ∧
        0 < S.cusp.epsilon :=
  ⟨SourceDefinition31Data.section_map_bijective S,
    SourceDefinition31Data.finite_place_data S,
    SourceDefinition31Data.infinite_place_data S,
    SourceDefinition31Data.cusp_positive S⟩

/-- Genuine assembly theorem: section/local-group clause package. -/
theorem sourceSectionClause_package {l : PrimeGeFive} (S : SourceDefinition31Data l) :
    Function.LeftInverse S.sections.sectionRightInverse S.sections.sectionMap ∧
      Function.RightInverse S.sections.sectionRightInverse S.sections.sectionMap ∧
        S.cusp.epsilon ≠ 0 :=
  ⟨S.sections.section_left_inverse, S.sections.section_right_inverse,
    SourceCuspClause.epsilon_ne_zero S.cusp⟩

end LeanFormal.IUT.XiFPaper.Mzk1SchemeSideAssemblyActual
end
