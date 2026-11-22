import LeanFormal.IUT.IUTII.Frobenioid.Example36GSetEtaleEquivalenceAssembly
import LeanFormal.IUT.IUTII.Frobenioid.Example36UnitNaturality

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36

open CategoryTheory CommAlgCat
open GSetToEtaleAlgebra

universe u
variable (K : Type u) [Field K]

/-- The actual equivalence between finite etale K-algebras and finite continuous
G_K-sets, assembled from the verified unit and counit natural isomorphisms. -/
noncomputable def finiteEtaleContinuousEquivalenceOfUnitCounit :
    (CommAlgCat.FiniteEtale K)ᵒᵖ ≌ FiniteContinuousGaloisSetCategory K :=
  CategoryTheory.Equivalence.mk
    (finiteEtaleToContinuousFunctor K)
    (continuousGaloisSetToFiniteEtaleFunctor K)
    (UnitNaturality.unitNatIso K)
    (continuousGaloisSetCounitNat K)

/-- The actual field Galois correspondence assembled from the equivalence. -/
noncomputable def fieldGaloisCorrespondenceOfUnitCounit :
    FieldGaloisCorrespondence K :=
  fieldGaloisCorrespondenceOfEquivalence K
    (finiteEtaleContinuousEquivalenceOfUnitCounit K)

end LeanFormal.IUT.IUTII.Frobenioid.Example36
