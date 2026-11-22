import tmp.sheaf.xif.paper.S2847A6ArithmeticActual
import tmp.sheaf.xif.paper.S2839A6F6ClauseRestatementActual
import tmp.sheaf.xif.paper.S2798StableEverywhere37Actual
import tmp.sheaf.xif.paper.S2786SignQuotientActual
import tmp.sheaf.xif.paper.S2793FieldOfModuliQiActual
import tmp.sheaf.xif.paper.S2766MaximalSolvableTopActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2839A6F6ClauseRestatementActual
open LeanFormal.IUT.XiFPaper.S2798StableEverywhere37Actual
open LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
open LeanFormal.IUT.XiFPaper.S2787ClauseB37Actual
open LeanFormal.IUT.XiFPaper.S2790F6Actual
open LeanFormal.IUT.XiFPaper.S2809E6FiniteActual
open LeanFormal.IUT.XiFPaper.S2782Curve37a1Actual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2840A6ClauseAActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance : NumberField S2790F6 := S2809_numberField

/-- Generic base-change formula for the j-invariant. -/
theorem S2840_baseChange_jInvariant
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (X : PuncturedEllipticCurve F) :
    (X.baseChange K).jInvariant = algebraMap F K X.jInvariant := by
  change (X.curve.map (algebraMap F K)).j = algebraMap F K X.curve.j
  exact WeierstrassCurve.map_j X.curve (algebraMap F K)

/-- 37a1 j-invariant over Q. -/
theorem S2840E37a1Q_j : E37a1Q.jInvariant = (110592 / 37 : ℚ) := by
  rw [PuncturedEllipticCurve.jInvariant_spec]
  change E37a1CurveQ.j = (110592 / 37 : ℚ)
  norm_num [E37a1CurveQ, WeierstrassCurve.j, WeierstrassCurve.c₄,
    WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- A6 curve j-invariant. -/
theorem S2840A6Curve_j :
    A6Curve.jInvariant = algebraMap ℚ S2847A6.F (110592 / 37) := by
  rw [A6Curve, S2840_baseChange_jInvariant, S2840_baseChange_jInvariant,
    S2840E37a1Q_j]
  letI : Algebra GaussianField S2847A6.F :=
    inferInstanceAs (Algebra GaussianField S2847F6)
  exact IsScalarTower.algebraMap_apply ℚ GaussianField S2847A6.F (110592 / 37)

/-- The A6 curve of S2847 is definitionally the S2839 A6Curve. -/
theorem S2840A6_curve_eq_zero : S2847A6.curve = A6Curve := rfl

/-- A6 j-invariant for S2847A6. -/
theorem S2840A6_j :
    S2847A6.curve.jInvariant = algebraMap ℚ S2847A6.F (110592 / 37) := by
  rw [S2840A6_curve_eq_zero]
  change A6Curve.jInvariant = algebraMap ℚ (A6F6 : Type) (110592 / 37)
  exact S2840A6Curve_j

/-- Weierstrass-curve equality between A6Curve and the F6-base-change of the
Gaussian 37a1 curve. -/
theorem S2840A6_curve_eq :
    A6Curve.curve = (E37QiPunctured.baseChange S2847F6).curve := by
  ext <;> simp [A6Curve, E37QiPunctured, E37Qi, E37, E37a1Q, E37a1CurveQ,
    S2790E, S2790A, S2787Arithmetic, WeierstrassCurve.baseChange,
    WeierstrassCurve.map]

/-- Stable reduction everywhere for A6, from S2798 over Q(i) by base change. -/
theorem S2840A6_stable :
    S2847A6.curve.HasStableReductionEverywhere := by
  have h := PuncturedEllipticCurve.hasStableReductionEverywhere_baseChange
    (X := E37QiPunctured) (K := S2847F6) S2798_hasStableReductionEverywhere
  rw [S2840A6_curve_eq_zero]
  unfold PuncturedEllipticCurve.HasStableReductionEverywhere at h ⊢
  unfold PuncturedEllipticCurve.HasStableReductionAt at h ⊢
  unfold PuncturedEllipticCurve.HasGoodReductionAt PuncturedEllipticCurve.HasMultiplicativeReductionAt
    at h ⊢
  simp only [NumberFieldFinitePlace.underlyingPrime] at h ⊢
  rw [S2840A6_curve_eq]
  exact h

/-- Field of moduli for A6. -/
noncomputable def S2840FieldOfModuli :
    SourceFieldOfModuli S2847A6 where
  jModuli := algebraMap ℚ S2847A6.F (110592 / 37)
  algebraMap_jModuli := by
    change algebraMap S2847A6.F S2847A6.F
      (algebraMap ℚ S2847A6.F (110592 / 37)) = S2847A6.curve.jInvariant
    rw [S2840A6_j]
    simp

/-- Top maximal solvable subextension of F6 over F6. -/
noncomputable def S2840TopMaxSolvable :
    isFiniteSolvableGaloisSubextension
      (⊤ : IntermediateField S2847A6.F S2847A6.F) := by
  refine ⟨?_, ?_, ?_⟩
  · exact inferInstance
  · exact inferInstance
  · haveI : Subsingleton
        ((⊤ : IntermediateField S2847A6.F S2847A6.F) ≃ₐ[S2847A6.F]
          (⊤ : IntermediateField S2847A6.F S2847A6.F)) :=
      ⟨fun f g => AlgEquiv.ext fun x => by
        have hx : x = algebraMap S2847A6.F
            (⊤ : IntermediateField S2847A6.F S2847A6.F) (x : S2847A6.F) := rfl
        rw [hx, AlgEquiv.commutes, AlgEquiv.commutes]⟩
    exact isSolvable_of_subsingleton _

/-- ClauseA for A6, conditional only on S. -/
noncomputable def S2840ClauseA
    (S : SourceSignQuotientData S2847A6) :
    SourceClauseA S2847A6 S where
  stable_reduction_nonarchimedean := fun _ => S2840A6_stable _
  field_of_moduli := S2840FieldOfModuli
  maximal_solvable_extension := ⊤
  maximal_solvable_property := S2840TopMaxSolvable
  maximal_solvable_contains := fun _ _ => le_top

#check S2840A6_j
#check S2840A6_stable
#check S2840FieldOfModuli
#check S2840TopMaxSolvable
#check S2840ClauseA
#print axioms S2840A6_stable
#print axioms S2840ClauseA

end LeanFormal.IUT.XiFPaper.S2840A6ClauseAActual
end
