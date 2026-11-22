import tmp.sheaf.xif.paper.S1746FiniteEtaleQuotientsActual

open CategoryTheory CategoryTheory.Limits

abbrev TestFiniteEtaleAlg (K : Type) [Field K] : Type 1 :=
  (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ

example (K : Type) [Field K] (G : Type) [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) (TestFiniteEtaleAlg K) := by
  infer_instance