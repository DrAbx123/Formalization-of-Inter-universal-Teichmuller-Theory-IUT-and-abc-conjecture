import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import LeanFormal.IUT.Foundations.Geometry.LocalReduction
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import LeanFormal.IUT.Foundations.Geometry.TatePointQuotientBoundary
import Mathlib.Tactic

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2787ClauseB37Actual

local instance s2787GaussianFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- 37a1 over QQ: y^2 + y = x^3 - x. -/
def E37a1CurveQ : WeierstrassCurve ℚ :=
  WeierstrassCurve.mk 0 0 1 (-1) 0

theorem E37a1CurveQ_discriminant : E37a1CurveQ.Δ = 37 := by
  norm_num [E37a1CurveQ, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance E37a1CurveQ_isElliptic : E37a1CurveQ.IsElliptic :=
  ⟨by rw [isUnit_iff_ne_zero, E37a1CurveQ_discriminant]; norm_num⟩

/-- The punctured 37a1 over QQ. -/
def E37a1Q : PuncturedEllipticCurve ℚ where
  curve := E37a1CurveQ
  isElliptic := E37a1CurveQ_isElliptic
  puncture := ⟨WeierstrassCurve.Projective.nonsingularLift_zero⟩

/-- The Gaussian arithmetic with 37a1 base change: Fmod = F = K = QQ(i). -/
noncomputable def S2787Arithmetic : InitialThetaArithmeticData fiveLabel where
  Fmod := GaussianField
  F := GaussianField
  K := GaussianField
  tower := gaussianIdentityThetaTower fiveLabel
  curve := E37a1Q.baseChange GaussianField

/-- The three Clause-B fields for 37a1 at the bad primes above 37, exposed
as an explicit interface (no ClauseA/C construction is hidden here). -/
structure S2787ClauseBData
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (S : SourceSignQuotientData A) (C : SourceClauseA A S) where
  multiplicative :
    forall p : NumberField.FinitePlace A.F,
      NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad ->
      A.curve.HasMultiplicativeReductionAt p
  qWitness :
    forall (p : NumberField.FinitePlace A.F)
      (_hp : NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad),
      Nonempty (SourceTateComparisonWitness A p)
  residueCoprime :
    forall (p : NumberField.FinitePlace A.F)
      (_hp : NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad),
      Nat.Coprime l.value
        (NumberFieldFinitePlace.residueCharacteristic
          (NumberFieldFinitePlace.comap (k := A.Fmod) p))

/-- Actual constructor: the three fields are exactly SourceClauseB. -/
theorem S2787ClauseB_of_data
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A} {C : SourceClauseA A S}
    (D : S2787ClauseBData S C) : SourceClauseB A S C where
  multiplicative_over_bad := D.multiplicative
  q_comparison := D.qWitness
  residue_characteristic_prime_to_l := D.residueCoprime

#check E37a1CurveQ
#check E37a1Q
#check S2787Arithmetic
#check S2787ClauseBData
#check S2787ClauseB_of_data

end LeanFormal.IUT.XiFPaper.S2787ClauseB37Actual
end