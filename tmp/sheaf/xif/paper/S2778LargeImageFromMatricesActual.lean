import tmp.sheaf.xif.paper.S2771Gap1ClosedActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceTorsionCarrierReduction
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2778LargeImageFromMatricesActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual

/-- Generic large-image transfer from explicit generators: if the matrices M
generate SL2 inside GL2 and their range lies in the Galois representation's
range, then the full SL2 image lies in that range. -/
theorem S2778_sl2_le_range_of_generators
    {F : Type*} [Field F] {ι : Type*} (X : PuncturedEllipticCurve F)
    (l : PrimeGeFive)
    (M : ι → Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value))
    (b : (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] X.LTorsion l)
    (hgen : Subgroup.map Matrix.SpecialLinearGroup.toGL
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      Subgroup.closure (Set.range M))
    (hsub : Set.range M ⊆
      (X.galoisLTorsionMatrixRepresentation l b).range) :
    Subgroup.map Matrix.SpecialLinearGroup.toGL
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      (X.galoisLTorsionMatrixRepresentation l b).range :=
  hgen.trans ((Subgroup.closure_le (K := (X.galoisLTorsionMatrixRepresentation l b).range)).2 hsub)

/-- Generic Serre-style large-image statement from explicit matrices. -/
theorem S2778_serreStyleLargeImage_of_matrices
    {F : Type*} [Field F] {ι : Type*} (X : PuncturedEllipticCurve F)
    (l : PrimeGeFive)
    (M : ι → Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value))
    (b : (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] X.LTorsion l)
    (hgen : Subgroup.map Matrix.SpecialLinearGroup.toGL
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      Subgroup.closure (Set.range M))
    (hsub : Set.range M ⊆
      (X.galoisLTorsionMatrixRepresentation l b).range) :
    InitialThetaSource.TorsionCarrierReduction.SerreStyleLargeImageStatement X l :=
  ⟨b, S2778_sl2_le_range_of_generators X l M b hgen hsub⟩

/-- The basis chosen from S2771 for the concrete prime 5. -/
noncomputable def S2778_fiveBasis
    {F : Type*} [Field F] [CharZero F] (X : PuncturedEllipticCurve F) :
    (Fin 2 → ZMod S2771FiveLabel.value) ≃ₗ[ZMod S2771FiveLabel.value]
      X.LTorsion S2771FiveLabel :=
  Classical.choice (S2771_rankTwoTorsionBasis X)

/-- The large-image statement at l = 5, using the S2771 basis. -/
theorem S2778_serreStyleLargeImage_five
    {F : Type*} [Field F] [CharZero F] {ι : Type*}
    (X : PuncturedEllipticCurve F)
    (M : ι → Matrix.GeneralLinearGroup (Fin 2) (ZMod S2771FiveLabel.value))
    (hgen : Subgroup.map Matrix.SpecialLinearGroup.toGL
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod S2771FiveLabel.value))) ≤
      Subgroup.closure (Set.range M))
    (hsub : Set.range M ⊆
      (X.galoisLTorsionMatrixRepresentation S2771FiveLabel
        (S2778_fiveBasis X)).range) :
    InitialThetaSource.TorsionCarrierReduction.SerreStyleLargeImageStatement X S2771FiveLabel :=
  S2778_serreStyleLargeImage_of_matrices X S2771FiveLabel M
    (S2778_fiveBasis X) hgen hsub

#check S2778_sl2_le_range_of_generators
#check S2778_serreStyleLargeImage_of_matrices
#check S2778_fiveBasis
#check S2778_serreStyleLargeImage_five
#print axioms S2778_serreStyleLargeImage_of_matrices
#print axioms S2778_serreStyleLargeImage_five

end LeanFormal.IUT.XiFPaper.S2778LargeImageFromMatricesActual
end
