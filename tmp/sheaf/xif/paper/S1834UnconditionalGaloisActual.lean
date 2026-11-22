import tmp.sheaf.xif.paper.S1819G3IntegratedActual
import tmp.sheaf.xif.paper.S1826BCPullbacksCoherenceActual
import Mathlib.Topology.Category.FinTopCat

/-!
# S1834: unconditional GaloisCategory on finite etale K-algebras

S1819 supplies the unconditional PreGaloisCategory; S1826 supplies the last
base-change condition, hence the geometric fibre functor.
-/

noncomputable section
open CategoryTheory
open scoped FintypeCatDiscrete

namespace S1834

open S1793GaloisAssembly

theorem galoisCategory (K : Type) [Field K] :
    GaloisCategory (S1793GaloisAssembly.FiniteEtaleAlg K) := by
  let hMono : S1793GaloisAssembly.MonoInducesIsoOnDirectSummandField K :=
    S1819.monoInducesIsoOnDirectSummandField_S1793 (K := K)
  letI hPre : PreGaloisCategory (S1793GaloisAssembly.FiniteEtaleAlg K) :=
    S1793GaloisAssembly.preGaloisCategory (K := K) hMono
  letI hPre' : PreGaloisCategory (S1769.C K) :=
    S1819.preGaloisCategory (K := K)
  have hFiber : S1793GaloisAssembly.FiberFunctorField K hPre := by
    change PreGaloisCategory.FiberFunctor (S1793GaloisAssembly.geometricFiber K)
    exact S1826.fiberFunctorUnconditional (K := K)
  exact S1793GaloisAssembly.galoisCategory (K := K) hMono hFiber

noncomputable def galoisEquivalence (K : Type) [Field K] :
    S1793GaloisAssembly.FiniteEtaleAlg K ≌
      ContAction FintypeCat.{0} (Aut (S1793GaloisAssembly.geometricFiber K)) := by
  let hMono : S1793GaloisAssembly.MonoInducesIsoOnDirectSummandField K :=
    S1819.monoInducesIsoOnDirectSummandField_S1793 (K := K)
  letI hPre : PreGaloisCategory (S1793GaloisAssembly.FiniteEtaleAlg K) :=
    S1793GaloisAssembly.preGaloisCategory (K := K) hMono
  letI hPre' : PreGaloisCategory (S1769.C K) :=
    S1819.preGaloisCategory (K := K)
  have hFiber : S1793GaloisAssembly.FiberFunctorField K hPre := by
    change PreGaloisCategory.FiberFunctor (S1793GaloisAssembly.geometricFiber K)
    exact S1826.fiberFunctorUnconditional (K := K)
  exact S1793GaloisAssembly.galoisEquivalence (K := K) hMono hFiber

end S1834

#print axioms S1834.galoisCategory
#print axioms S1834.galoisEquivalence
