import tmp.sheaf.xif.paper.S2826Torsion23Fresh
import tmp.sheaf.xif.paper.S2771Gap1ClosedActual
import tmp.sheaf.xif.paper.S2809E6FiniteActual
import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2790F6Actual
open LeanFormal.IUT.XiFPaper.S2809E6FiniteActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s2847F6NumberField : NumberField ↥S2790F6 := S2809_numberField

/-- The base F6 = Q(i, E[6]) as a number field. -/
abbrev S2847F6 : Type := ↥S2790F6

instance : Field S2847F6 := inferInstance
instance : NumberField S2847F6 := s2847F6NumberField

/-- The S2790E curve base-changed to F6. -/
noncomputable abbrev S2847Curve : PuncturedEllipticCurve S2847F6 :=
  S2790E.baseChange S2847F6

/-- S2771 rank-two 5-torsion basis over F6. -/
noncomputable def S2847Basis :
    (Fin 2 → ZMod S2771FiveLabel.value) ≃ₗ[ZMod S2771FiveLabel.value]
      S2847Curve.LTorsion S2771FiveLabel :=
  Classical.choice (S2771_rankTwoTorsionBasis S2847Curve)

/-- The E[5]-kernel field over F6. -/
noncomputable def S2847K : IntermediateField S2847F6 (AlgebraicClosure S2847F6) :=
  S2847Curve.galoisLTorsionKernelField S2771FiveLabel S2847Basis

instance : Field S2847K := inferInstance
instance : NumberField S2847K :=
  S2847Curve.galoisLTorsionKernelField_numberField S2771FiveLabel S2847Basis
instance : Algebra S2847F6 S2847K := inferInstance
instance : FiniteDimensional S2847F6 S2847K :=
  S2847Curve.galoisLTorsionKernelField_finiteDimensional S2771FiveLabel S2847Basis
instance : IsGalois S2847F6 S2847K :=
  S2847Curve.galoisLTorsionKernelField_isGalois S2771FiveLabel S2847Basis

/-- HasSqrtNegOne on F6, transported from GaussianField. -/
theorem S2847_hasSqrtNegOne : HasSqrtNegOne S2847F6 := by
  obtain ⟨i, hi⟩ := gaussianField_sqrtNegOne
  refine ⟨algebraMap GaussianField S2847F6 i, ?_⟩
  rw [← map_mul, hi, map_neg, map_one]

/-- The F6 -> F6 -> K tower. -/
noncomputable def S2847Tower :
    ThetaFieldTower S2771FiveLabel S2847F6 S2847F6 S2847K where
  sqrtNegOne := S2847_hasSqrtNegOne
  degreePrimeToL := by
    rw [Module.finrank_self]
    exact Nat.coprime_one_left _

/-- A6: Fmod = F = F6, K = E[5]-kernel field over F6, curve = E37/F6. -/
noncomputable def S2847A6 : InitialThetaArithmeticData S2771FiveLabel where
  Fmod := S2847F6
  fieldFmod := inferInstance
  numberFieldFmod := inferInstance
  F := S2847F6
  fieldF := inferInstance
  numberFieldF := inferInstance
  K := S2847K
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
  tower := S2847Tower
  curve := S2847Curve

/-- S2826_torsion23 is exactly the A6 curve's Torsion23Rational. -/
theorem S2847_torsion23 : S2847A6.curve.Torsion23Rational :=
  S2826_torsion23

#check S2847A6
#check S2847_torsion23
#print axioms S2847A6
#print axioms S2847_torsion23

end LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
end
