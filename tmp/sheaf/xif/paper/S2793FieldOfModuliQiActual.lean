import tmp.sheaf.xif.paper.S2782Curve37a1Actual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import Mathlib.GroupTheory.SpecificGroups.ZGroup

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open Polynomial
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2793FieldOfModuliQiActual

open LeanFormal.IUT.XiFPaper.S2782Curve37a1Actual

local instance S2793FactIrr :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance S2793Quadratic : Algebra.IsQuadraticExtension ℚ GaussianField where
  finrank_eq_two' := LeanFormal.IUT.IUTII.Frobenioid.Example36.gaussianField_finrank

example : IsGalois ℚ GaussianField := inferInstance

def S2793FiveLabel : PrimeGeFive where
  value := 5
  prime := by norm_num
  ge_five := by norm_num

instance S2793E37Qi_isElliptic : E37Qi.IsElliptic := by
  change (E37.map (algebraMap ℚ GaussianField)).IsElliptic
  infer_instance

def E37QiPunctured : PuncturedEllipticCurve GaussianField where
  curve := E37Qi
  isElliptic := inferInstance
  puncture := ⟨WeierstrassCurve.Projective.nonsingularLift_zero⟩

noncomputable def S2793Tower :
    ThetaFieldTower S2793FiveLabel ℚ GaussianField GaussianField where
  sqrtNegOne := gaussianField_sqrtNegOne
  degreePrimeToL := by
    rw [LeanFormal.IUT.IUTII.Frobenioid.Example36.gaussianField_finrank]
    norm_num [S2793FiveLabel]

noncomputable def S2793Arithmetic :
    InitialThetaArithmeticData S2793FiveLabel where
  Fmod := ℚ
  fieldFmod := inferInstance
  numberFieldFmod := inferInstance
  F := GaussianField
  fieldF := inferInstance
  numberFieldF := inferInstance
  K := GaussianField
  fieldK := inferInstance
  numberFieldK := inferInstance
  algebraFmodF := inferInstance
  algebraFK := inferInstance
  algebraFmodK := inferInstance
  towerFmodFK := inferInstance
  finiteFmodF := inferInstance
  galoisFmodF := inferInstance
  finiteFK := inferInstance
  galoisFK := inferInstance
  tower := S2793Tower
  curve := E37QiPunctured

theorem E37Qi_j : E37Qi.j = (110592 / 37 : GaussianField) := by
  rw [WeierstrassCurve.j]
  have hΔ : E37Qi.Δ' = Units.mk0 (37 : GaussianField) (by norm_num) :=
    Units.ext E37Qi_discriminant
  rw [hΔ, E37Qi_c4]
  norm_num

noncomputable def S2793FieldOfModuli : SourceFieldOfModuli S2793Arithmetic where
  jModuli := (110592 / 37 : ℚ)
  algebraMap_jModuli := by
    change algebraMap ℚ GaussianField (110592 / 37 : ℚ) = E37Qi.j
    rw [E37Qi_j]
    norm_num

/-- The Q -> Q(i) maximal-solvable-extension placeholder: the whole field Q(i). -/
def S2793MaximalSolvableExtension : IntermediateField ℚ GaussianField := ⊤

theorem S2793MaximalSolvable_finiteDimensional :
    FiniteDimensional ℚ S2793MaximalSolvableExtension :=
  inferInstance

theorem S2793MaximalSolvable_isGalois :
    IsGalois ℚ S2793MaximalSolvableExtension := by
  let e : S2793MaximalSolvableExtension ≃ₐ[ℚ] GaussianField :=
    IntermediateField.topEquiv
  exact e.transfer_galois.mpr inferInstance

theorem S2793MaximalSolvable_isSolvable :
    IsSolvable (S2793MaximalSolvableExtension ≃ₐ[ℚ]
      S2793MaximalSolvableExtension) := by
  let e : S2793MaximalSolvableExtension ≃ₐ[ℚ] GaussianField :=
    IntermediateField.topEquiv
  haveI hgal : IsGalois ℚ S2793MaximalSolvableExtension :=
    e.transfer_galois.mpr inferInstance
  haveI : Fintype (S2793MaximalSolvableExtension ≃ₐ[ℚ]
      S2793MaximalSolvableExtension) :=
    AlgEquiv.fintype ℚ S2793MaximalSolvableExtension
  have hcard : Nat.card (S2793MaximalSolvableExtension ≃ₐ[ℚ]
      S2793MaximalSolvableExtension) = 2 := by
    rw [IsGalois.card_aut_eq_finrank]
    change Module.finrank ℚ (⊤ : IntermediateField ℚ GaussianField) = 2
    rw [IntermediateField.finrank_top',
      LeanFormal.IUT.IUTII.Frobenioid.Example36.gaussianField_finrank]
  haveI : IsZGroup (S2793MaximalSolvableExtension ≃ₐ[ℚ]
      S2793MaximalSolvableExtension) :=
    IsZGroup.of_squarefree (by rw [hcard]; exact Nat.prime_two.squarefree)
  infer_instance

theorem S2793MaximalSolvable_le_top
    (E : IntermediateField ℚ GaussianField) :
    E ≤ S2793MaximalSolvableExtension :=
  le_top

#check S2793Arithmetic
#check S2793FieldOfModuli
#print axioms S2793FieldOfModuli

end LeanFormal.IUT.XiFPaper.S2793FieldOfModuliQiActual
end
