import tmp.sheaf.xif.paper.S1793GaloisAssemblyWithQuotientsActual

open CategoryTheory CategoryTheory.Limits

-- The delivered theorems, at the exact category of the task.
#check @S1793GaloisAssembly.preGaloisCategory
#check @S1793GaloisAssembly.galoisCategory
#check @S1793GaloisAssembly.galoisEquivalence
#check @S1793GaloisAssembly.hasQuotientsByFiniteGroupsField_holds
#print axioms S1793GaloisAssembly.preGaloisCategory
#print axioms S1793GaloisAssembly.galoisCategory

-- The hypothesis-free part: the four actual fields of the assembled instance.
example {K : Type} [Field K] (hMono : S1793GaloisAssembly.MonoInducesIsoOnDirectSummandField K) :
    PreGaloisCategory ((CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) :=
  S1793GaloisAssembly.preGaloisCategory hMono

example {K : Type} [Field K] (hMono : S1793GaloisAssembly.MonoInducesIsoOnDirectSummandField K)
    (hFiber : S1793GaloisAssembly.FiberFunctorField K
      (S1793GaloisAssembly.preGaloisCategory hMono)) :
    GaloisCategory ((CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) :=
  S1793GaloisAssembly.galoisCategory hMono hFiber
