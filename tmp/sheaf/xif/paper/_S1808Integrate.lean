import Mathlib.RingTheory.Etale.Finite
import tmp.sheaf.xif.paper._S1808Dev
import tmp.sheaf.xif.paper.S1786G3CategoricalTransferActual
import tmp.sheaf.xif.paper.S1793GaloisAssemblyWithQuotientsActual

noncomputable section
open CategoryTheory

namespace S1808

theorem monoInducesIsoOnDirectSummand (K : Type) [Field K] :
    S1786.MonoInducesIsoOnDirectSummandField K :=
  S1786.monoInducesIsoOnDirectSummand_of_epiSurjective_of_surjectiveSplit
    (epiSurjective K) (surjectiveSplit K)

theorem monoInducesIsoOnDirectSummand' (K : Type) [Field K] :
    S1793GaloisAssembly.MonoInducesIsoOnDirectSummandField K :=
  monoInducesIsoOnDirectSummand K

example (K : Type) [Field K] :
    S1793GaloisAssembly.FiniteEtaleAlg K = (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ := rfl

theorem preGaloisCategory (K : Type) [Field K] :
    PreGaloisCategory (S1793GaloisAssembly.FiniteEtaleAlg K) :=
  S1793GaloisAssembly.preGaloisCategory (K := K) (monoInducesIsoOnDirectSummand K)

theorem preGaloisCategory' (K : Type) [Field K] :
    PreGaloisCategory ((CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) :=
  preGaloisCategory K

theorem galoisCategory (K : Type) [Field K]
    (hFiber : S1793GaloisAssembly.FiberFunctorField K
      (S1793GaloisAssembly.preGaloisCategory (K := K) (monoInducesIsoOnDirectSummand K))) :
    GaloisCategory (S1793GaloisAssembly.FiniteEtaleAlg K) :=
  S1793GaloisAssembly.galoisCategory (K := K) (monoInducesIsoOnDirectSummand K) hFiber

end S1808

#print axioms S1808.epiSurjective
#print axioms S1808.surjectiveSplit
#print axioms S1808.monoInducesIsoOnDirectSummand
#print axioms S1808.monoInducesIsoOnDirectSummand'
#print axioms S1808.preGaloisCategory
#print axioms S1808.preGaloisCategory'
#print axioms S1808.galoisCategory
