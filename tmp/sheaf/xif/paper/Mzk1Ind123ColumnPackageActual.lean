import LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceColumnCarrierIdentification

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1Ind123ColumnPackageActual — A480 real consumer packages (Ind1/2/3 column realization)

New joint conclusions combining the donor laws of
`SourceColumnCarrierIdentification.lean` (:114/:125/:144/:163/:192):

1. `ind_rotate_package`: the (Ind1) and (Ind2) rotation laws hold jointly
   under the two-label commutativity hypothesis;
2. `columnRealization_ind12_package`: the (Ind1) and (Ind2) intertwinings of the
   canonical column realization hold jointly;
3. `columnRealization_all_package`: additionally the (Ind3) intertwining holds
   under the explicit side condition `x.level.val + n ≤ N`.

No sorry/axioms; no closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Ind123ColumnPackageActual

open LeanFormal.IUT
open LeanFormal.IUT.ConcreteFiniteTheorem311
open LeanFormal.IUT.ConcreteFiniteStepXI
open LeanFormal.IUT.SourceColumnRealization

/-- Joint (Ind1)/(Ind2) rotation package. -/
theorem ind_rotate_package {Label : Type*} {Choice : Type*} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) {a b : Label}
    (h : b + a = a + b) (c : Choice) :
    core.ind1 a (core.ind1 b c) = core.ind1 b (core.ind1 a c) ∧
      core.ind2 a (core.ind2 b c) = core.ind2 b (core.ind2 a c) :=
  ⟨core_ind1_rotate_of_comm core h c, core_ind2_rotate_of_comm core h c⟩

/-- Joint (Ind1)/(Ind2) intertwining package of the column realization. -/
theorem columnRealization_ind12_package {l : PrimeGeFive} {N : Nat}
    {Label : Type*} {Choice : Type*} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) (t : finiteLabel l) (x : FiniteColumnIndex l N) :
    coreColumnRealization core φ c₀ (FiniteColumnIndex.ind1 t x) =
        core.ind1 (φ t) (coreColumnRealization core φ c₀ x) ∧
      coreColumnRealization core φ c₀ (FiniteColumnIndex.ind2 t x) =
        core.ind2 (φ t) (coreColumnRealization core φ c₀ x) :=
  ⟨coreColumnRealization_ind1 core φ c₀ t x,
   coreColumnRealization_ind2 core φ c₀ t x⟩

/-- Full (Ind1)/(Ind2)/(Ind3) intertwining package (Ind3 with side condition). -/
theorem columnRealization_all_package {l : PrimeGeFive} {N : Nat}
    {Label : Type*} {Choice : Type*} [AddGroup Label]
    (core : MultiradialKernel.Core Label Choice) (φ : finiteLabel l →+ Label)
    (c₀ : Choice) (t : finiteLabel l) (x : FiniteColumnIndex l N)
    (n : Nat) (h : x.level.val + n ≤ N) :
    coreColumnRealization core φ c₀ (FiniteColumnIndex.ind1 t x) =
        core.ind1 (φ t) (coreColumnRealization core φ c₀ x) ∧
      coreColumnRealization core φ c₀ (FiniteColumnIndex.ind2 t x) =
        core.ind2 (φ t) (coreColumnRealization core φ c₀ x) ∧
      coreColumnRealization core φ c₀ (FiniteColumnIndex.ind3 n x) =
        core.ind3 n (coreColumnRealization core φ c₀ x) :=
  ⟨coreColumnRealization_ind1 core φ c₀ t x,
   coreColumnRealization_ind2 core φ c₀ t x,
   coreColumnRealization_ind3 core φ c₀ n x h⟩

#check ind_rotate_package
#check columnRealization_all_package

end LeanFormal.IUT.XiFPaper.Mzk1Ind123ColumnPackageActual
end