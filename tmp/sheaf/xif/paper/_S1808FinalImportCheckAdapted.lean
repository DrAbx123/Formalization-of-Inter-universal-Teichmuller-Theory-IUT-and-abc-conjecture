import tmp.sheaf.xif.paper.S1808G3FinalActual

noncomputable section
open CategoryTheory

#check @S1808.epiSurjective
#check @S1808.surjectiveSplit
#check @S1808.monoInducesIsoOnDirectSummand
#check @S1808.monoInducesIsoOnDirectSummand'
#check @S1808.preGaloisCategory
#check @S1808.preGaloisCategory' 
#check @S1808.galoisCategory

example (K : Type) [Field K] : S1747.EpiSurjective K := S1808.epiSurjective K
example (K : Type) [Field K] : S1747.SurjectiveSplit K := S1808.surjectiveSplit K
example (K : Type) [Field K] : S1786.MonoInducesIsoOnDirectSummandField K :=
  S1808.monoInducesIsoOnDirectSummand K
example (K : Type) [Field K] : PreGaloisCategory ((CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) :=
  S1808.preGaloisCategory' K
