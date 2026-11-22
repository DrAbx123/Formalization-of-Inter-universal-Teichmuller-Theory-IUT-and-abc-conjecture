import tmp.sheaf.xif.paper.S1719D5AllActual
import tmp.sheaf.xif.paper.S1711RationalSplitAtFiveBridge
import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1717PlaceSevenD5Actual

namespace Probe10

def P10 : ℚ[X] := X ^ 2 + 1
def H10 : ℚ[X] := S1687H * P10
abbrev F10 : Type := Polynomial.SplittingField H10
local instance : DecidableEq F10 := Classical.decEq _

instance : NumberField F10 where
  to_charZero := inferInstance
  to_finiteDimensional := by
    letI : IsSplittingField ℚ F10 H10 := Polynomial.IsSplittingField.splittingField H10
    exact Polynomial.IsSplittingField.finiteDimensional F10 H10

theorem H10_splits : (H10.map (algebraMap ℚ F10)).Splits := Polynomial.SplittingField.splits H10

theorem P10_splits : (P10.map (algebraMap ℚ F10)).Splits := by
  have hf : ((S1687H * P10).map (algebraMap ℚ F10)).Splits := by
    simpa [H10] using H10_splits
  rw [Polynomial.map_mul] at hf
  rw [Polynomial.splits_mul'] at hf
  exact hf.2.resolve_right (by
    intro h
    exact S1687H_map_ne_zero (by simpa using h))

theorem P10_degree : P10.degree = (2 : WithBot ℕ) := by
  unfold P10; compute_degree!

theorem hasSqrt : HasSqrtNegOne F10 := by
  have hdeg : (P10.map (algebraMap ℚ F10)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (algebraMap ℚ F10).injective, P10_degree]
    norm_num
  let r : F10 := Polynomial.rootOfSplits P10_splits hdeg
  have hr : Polynomial.eval r (P10.map (algebraMap ℚ F10)) = 0 :=
    Polynomial.eval_rootOfSplits P10_splits hdeg
  have hr' : Polynomial.aeval r P10 = 0 := by
    simpa [Polynomial.aeval_def, Polynomial.eval_map] using hr
  refine ⟨r, ?_⟩
  have h : r ^ 2 + 1 = 0 := by simpa [P10] using hr'
  rw [pow_two] at h
  linear_combination h

abbrev Curve10 : PuncturedEllipticCurve F10 := S1667Punctured.baseChange F10

noncomputable def PlaceFive : NumberField.FinitePlace F10 :=
  Classical.choose (NumberFieldFinitePlace.comap_surjective (k := ℚ) (K := F10) concreteFivePlace)

theorem PlaceFive_comap : NumberFieldFinitePlace.comap (k := ℚ) PlaceFive = concreteFivePlace :=
  Classical.choose_spec (NumberFieldFinitePlace.comap_surjective (k := ℚ) (K := F10) concreteFivePlace)

theorem splitFive : Curve10.HasSplitMultiplicativeReductionAt PlaceFive := by
  apply PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_baseChange
  rw [PlaceFive_comap]
  exact S1711RationalSplitAtFive

noncomputable def PlaceSeven : NumberField.FinitePlace F10 :=
  Classical.choose (NumberFieldFinitePlace.comap_surjective (k := ℚ) (K := F10) concreteSevenPlace)

theorem PlaceSeven_comap : NumberFieldFinitePlace.comap (k := ℚ) PlaceSeven = concreteSevenPlace :=
  Classical.choose_spec (NumberFieldFinitePlace.comap_surjective (k := ℚ) (K := F10) concreteSevenPlace)

theorem splitSeven : Curve10.HasSplitMultiplicativeReductionAt PlaceSeven := by
  apply PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_baseChange
  rw [PlaceSeven_comap]
  exact S1717_splitMultiplicativeReductionAtSeven


instance : IsGalois ℚ F10 := by
  rw [isGalois_iff]
  constructor
  · infer_instance
  · letI : IsSplittingField ℚ F10 H10 := Polynomial.IsSplittingField.splittingField H10
    infer_instance

def Tower10 (l : PrimeGeFive)
    (hcop : Nat.Coprime (Module.finrank ℚ F10) l.value) : ThetaFieldTower l ℚ F10 F10 where
  sqrtNegOne := hasSqrt
  degreePrimeToL := hcop

noncomputable def Arithmetic10 (l : PrimeGeFive)
    (hcop : Nat.Coprime (Module.finrank ℚ F10) l.value)
    (htor : PuncturedEllipticCurve.Torsion23Rational Curve10) :
    InitialThetaArithmeticData l where
  Fmod := ℚ
  F := F10
  K := F10
  tower := Tower10 l hcop
  curve := Curve10

example : IsGalois ℚ F10 := by
  rw [isGalois_iff]
  constructor
  · infer_instance
  · letI : IsSplittingField ℚ F10 H10 := Polynomial.IsSplittingField.splittingField H10
    infer_instance

example : IsGalois F10 F10 := inferInstance
example : FiniteDimensional F10 F10 := inferInstance


def Torsion23Missing : Prop := PuncturedEllipticCurve.Torsion23Rational Curve10

def BaseChangeMissing : Prop :=
  ∀ {k K : Type} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X : PuncturedEllipticCurve k),
    PuncturedEllipticCurve.Torsion23Rational X →
    PuncturedEllipticCurve.Torsion23Rational (X.baseChange K)

theorem paperCondition : S1667PaperConditionB F10 Curve10 = Torsion23Missing := rfl

def DegreeMissing (l : PrimeGeFive) : Prop :=
  Nat.Coprime (Module.finrank ℚ F10) l.value

end Probe10