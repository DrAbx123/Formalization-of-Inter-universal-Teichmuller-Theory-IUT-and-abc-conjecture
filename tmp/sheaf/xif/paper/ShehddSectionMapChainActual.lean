import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary

/-!
# ShehddSectionMapChainActual — place-partition label and section-map bijectivity chain

New chain consequences of the compiled boundary laws: bad-label equality is equivalent to
selected-label equality under the bad inclusion, and the section map / right inverse are
bijections (injectivity + surjectivity composed).  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddSectionMapChainActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

universe u

/-- **PROVED chain:** for a place partition, equality of bad labels is equivalent to
equality of the selected labels at the included places. -/
theorem placePartition_label_iff_chain {Selected Bad : Type u}
    (P : SourcePlacePartition Selected Bad) (b₁ b₂ : Bad) :
    P.badLabel b₁ = P.badLabel b₂ ↔
      P.selectedLabel (P.badIncluded b₁) = P.selectedLabel (P.badIncluded b₂) := by
  constructor
  · intro h
    exact P.bad_label_transport h
  · intro h
    rw [← P.badLabel_compatible b₁, ← P.badLabel_compatible b₂]
    exact h

/-- **PROVED chain:** the section map is a bijection (injectivity and surjectivity
composed). -/
theorem sectionMap_bijective_chain (S : SourceSectionClause) :
    Function.Bijective S.sectionMap :=
  ⟨S.sectionMap_injective, S.sectionMap_surjective⟩

/-- **PROVED chain:** the section right inverse is a bijection. -/
theorem sectionRightInverse_bijective_chain (S : SourceSectionClause) :
    Function.Bijective S.sectionRightInverse :=
  ⟨S.sectionRightInverse_injective, S.sectionRightInverse_surjective⟩

end LeanFormal.IUT.XiFPaper.ShehddSectionMapChainActual
end