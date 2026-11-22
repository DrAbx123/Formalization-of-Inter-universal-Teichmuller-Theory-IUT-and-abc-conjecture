import tmp.sheaf.xif.paper.S1811SurjectiveSplitDedicatedActual
import tmp.sheaf.xif.paper.S1786G3CategoricalTransferActual

/-! Consumer / comparator probe for S1811 (verification only, not a deliverable). -/

noncomputable section

-- the exact statement consumed by S1747/S1786
example (K : Type) [Field K] : S1747.SurjectiveSplit K := S1811.surjectiveSplit (K := K)

-- S1786.FiniteEtaleSplit from S1811 + the remaining missing input EpiSurjective
example (K : Type) [Field K] (hEpi : S1747.EpiSurjective K) : S1786.FiniteEtaleSplit K :=
  S1786.finiteEtaleSplit_of_epiSurjective_of_surjectiveSplit hEpi (S1811.surjectiveSplit (K := K))

-- the (G3) field of PreGaloisCategory
example (K : Type) [Field K] (hEpi : S1747.EpiSurjective K) :
    S1786.MonoInducesIsoOnDirectSummandField K :=
  S1786.monoInducesIsoOnDirectSummand_of_epiSurjective_of_surjectiveSplit hEpi
    (S1811.surjectiveSplit (K := K))

-- the actual PreGaloisCategory instance with this (G3) field
example (K : Type) [Field K]
    (hTerm : CategoryTheory.Limits.HasTerminal (S1786.FiniteEtaleAlg K))
    (hPull : CategoryTheory.Limits.HasPullbacks (S1786.FiniteEtaleAlg K))
    (hCoprod : CategoryTheory.Limits.HasFiniteCoproducts (S1786.FiniteEtaleAlg K))
    (hQuot : ∀ (G : Type) [Group G] [Finite G],
      CategoryTheory.Limits.HasColimitsOfShape (CategoryTheory.SingleObj G)
        (S1786.FiniteEtaleAlg K))
    (hEpi : S1747.EpiSurjective K) :
    CategoryTheory.PreGaloisCategory (S1786.FiniteEtaleAlg K) :=
  S1786.preGaloisCategory_of_fields hTerm hPull hCoprod hQuot hEpi
    (S1811.surjectiveSplit (K := K))

#print axioms S1811.surjectiveSplit
