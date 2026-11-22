import tmp.sheaf.xif.paper.S1797MonoSecondActual

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace S1797Check

example : S1747.EpiSurjective ℚ := S1797.epiSurjective
example : S1747.SurjectiveSplit ℚ := S1797.surjectiveSplit
example : S1786.FiniteEtaleSplit ℚ := S1797.finiteEtaleSplit
example : S1793GaloisAssembly.MonoInducesIsoOnDirectSummandField ℚ :=
  S1797.monoInducesIsoOnDirectSummandField_S1793
example : PreGaloisCategory ((CommAlgCat.FiniteEtale.{0} ℚ)ᵒᵖ) := S1797.preGaloisCategory
example (X Y : S1793GaloisAssembly.FiniteEtaleAlg (K := ℚ)) (i : X ⟶ Y) [Mono i] :
    ∃ (Z : S1793GaloisAssembly.FiniteEtaleAlg (K := ℚ)) (u : Z ⟶ Y),
      Nonempty (IsColimit (BinaryCofan.mk i u)) :=
  @PreGaloisCategory.monoInducesIsoOnDirectSummand _ _ S1797.preGaloisCategory X Y i _

end S1797Check