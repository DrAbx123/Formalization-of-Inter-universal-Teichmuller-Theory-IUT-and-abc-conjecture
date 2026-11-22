import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import LeanFormal.IUT.IUTII.Frobenioid.Example36EllipticCurveAnabelioid
import tmp.sheaf.xif.paper.S2766MaximalSolvableTopActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S2766MaximalSolvableTopActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

local instance s2773GaussianFact :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := by
  apply Fact.mk
  apply X_pow_sub_C_irreducible_of_prime (p := 2) Nat.prime_two
  intro b hb
  have hnonneg : 0 <= b ^ 2 := sq_nonneg b
  rw [hb] at hnonneg
  exact (not_le_of_gt (neg_lt_zero.mpr zero_lt_one)) hnonneg

namespace LeanFormal.IUT.XiFPaper.S2773ClauseAConditionalActual

variable {l : PrimeGeFive}

/-- The Gaussian curve y^2 = x^3 - x. -/
def gaussianCurve : PuncturedEllipticCurve GaussianField where
  curve := curveY2EqX3SubX.map (algebraMap ℚ GaussianField)
  isElliptic := inferInstance
  puncture := ⟨WeierstrassCurve.Projective.nonsingularLift_zero⟩

theorem gaussianCurve_j : gaussianCurve.curve.j = (1728 : GaussianField) := by
  rw [gaussianCurve, WeierstrassCurve.map_j]
  norm_num [curveY2EqX3SubX, WeierstrassCurve.j, WeierstrassCurve.c₄,
    WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The Gaussian arithmetic data attached to y^2 = x^3 - x. -/
def gaussianArithmetic : InitialThetaArithmeticData l where
  Fmod := GaussianField
  F := GaussianField
  K := GaussianField
  tower := gaussianIdentityThetaTower l
  curve := gaussianCurve

/-- The actual field-of-moduli datum j = 1728. -/
noncomputable def gaussianFieldOfModuli :
    SourceFieldOfModuli (gaussianArithmetic (l := l)) where
  jModuli := 1728
  algebraMap_jModuli := by
    change (1728 : GaussianField) = gaussianCurve.jInvariant
    rw [PuncturedEllipticCurve.jInvariant_spec, gaussianCurve_j]

/-- Conditional ClauseA: stable reduction is the remaining input, field of
moduli and maximal solvable extension are actual. -/
noncomputable def gaussianClauseA
    (S : SourceSignQuotientData (gaussianArithmetic (l := l)))
    (hstable : forall p : NumberField.FinitePlace GaussianField,
      gaussianCurve.HasStableReductionAt p) :
    SourceClauseA (gaussianArithmetic (l := l)) S where
  stable_reduction_nonarchimedean := hstable
  field_of_moduli := gaussianFieldOfModuli (l := l)
  maximal_solvable_extension := ⊤
  maximal_solvable_property := top_isFiniteSolvableGaloisSubextension
  maximal_solvable_contains := maximalSolvableContains_top

#check gaussianCurve
#check gaussianCurve_j
#check gaussianArithmetic
#check gaussianFieldOfModuli
#check gaussianClauseA
#print axioms gaussianClauseA

end LeanFormal.IUT.XiFPaper.S2773ClauseAConditionalActual
end
