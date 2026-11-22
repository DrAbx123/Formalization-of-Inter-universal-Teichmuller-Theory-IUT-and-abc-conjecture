import tmp.sheaf.xif.paper.S1822BCPullbacksActual

open CategoryTheory CategoryTheory.Limits

/-- Downstream check: the theorem is usable where S1769 needs it. -/
example (K : Type) [Field K] : S1769.BCPreservesPullbacks K :=
  S1822.S1769_BCPreservesPullbacks K

/-- Downstream check: the generic field-extension version. -/
example (K S : Type) [Field K] [Field S] [Algebra K S] :
    PreservesLimitsOfShape WalkingCospan
      (CommAlgCat.FiniteEtale.baseChange K S :
        CommAlgCat.FiniteEtale.{0} K ⥤ CommAlgCat.FiniteEtale.{0} S).op :=
  S1822.baseChange_op_preservesPullbacks K S

#print axioms S1822.BCPreservesPullbacks_holds
