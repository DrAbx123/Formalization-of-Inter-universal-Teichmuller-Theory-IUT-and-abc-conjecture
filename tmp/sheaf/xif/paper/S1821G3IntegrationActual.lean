import tmp.sheaf.xif.paper.S1747FiniteEtaleMonoSplitActual
import tmp.sheaf.xif.paper.S1771FiniteEtaleEpiSplitActual
import tmp.sheaf.xif.paper.S1810EpiSurjectiveDedicatedActual
import tmp.sheaf.xif.paper.S1786G3CategoricalTransferActual
import tmp.sheaf.xif.paper.S1793GaloisAssemblyWithQuotientsActual

/-!
# S1821: closing the finite-etale Galois category from S1810, S1771, S1786, S1793

S1810 proves S1747.EpiSurjective K; S1771 proves that a surjective map of
finite etale K-algebras is a product projection, which gives
S1747.SurjectiveSplit K; S1786 transfers the pair to the (G3) field; S1793
supplies the other four fields. This file records the resulting unconditional
PreGaloisCategory (FiniteEtaleAlg K).
-/

noncomputable section

namespace S1821

open S1747

/-- S1747.SurjectiveSplit K, obtained from S1771's product-projection theorem. -/
theorem surjectiveSplit (K : Type) [Field K] : S1747.SurjectiveSplit K := by
  intro A B hAR hAA hAF hAE hBR hBA hBF hBE phi hphi
  obtain ⟨C, hCR, hCA, hCF, hCE, e, he⟩ :=
    S1771FiniteEtaleEpiSplit.exists_prod_algEquiv_of_surjective
      (K := K) (A := A) (B := B) phi hphi
  exact ⟨C, hCR, hCA, hCF, hCE, e, he.symm⟩

/-- The (G3) field, now unconditional via S1810 + S1771 + S1786. -/
theorem g3 (K : Type) [Field K] :
    S1786.MonoInducesIsoOnDirectSummandField K :=
  S1786.monoInducesIsoOnDirectSummand_of_epiSurjective_of_surjectiveSplit
    (K := K) (S1810.epiSurjective (K := K)) (surjectiveSplit K)

/-- The unconditional PreGaloisCategory on finite etale K-algebras. -/
theorem preGaloisCategory (K : Type) [Field K] :
    PreGaloisCategory (S1793GaloisAssembly.FiniteEtaleAlg K) :=
  S1793GaloisAssembly.preGaloisCategory (K := K) (g3 K)

end S1821

#print axioms S1821.surjectiveSplit
#print axioms S1821.g3
#print axioms S1821.preGaloisCategory
