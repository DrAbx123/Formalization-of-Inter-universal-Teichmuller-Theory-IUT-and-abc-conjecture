import tmp.sheaf.xif.paper.S3119NegInvolutionAttempt
import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import tmp.sheaf.xif.paper.S1536SourceSignQuotientFromOrbicurveActual

noncomputable section
open LeanFormal.IUT CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionAttempt
open LeanFormal.IUT.XiFPaper.S3119GeometricCorePrefixAttempt
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 160000

namespace LeanFormal.IUT.XiFPaper.S3120StackAutoFaithfulTarget

variable {l : PrimeGeFive}

/-- Strict faithfulness of S1742StrongTransOfHom on scheme endomorphisms of the
S1419 representing scheme: equal induced strong transformations imply equal
scheme morphisms.  This is actual from the strict round-trip lemma. -/
theorem S3120StrongTransOfHom_injective
    (α β : S1419AffineOver (l := l) ⟶ S1419AffineOver (l := l))
    (h : S1742StrongTransOfHom (F := S1348K l) α =
      S1742StrongTransOfHom (F := S1348K l) β) :
    α = β := by
  have h' := congrArg
    (S1742HomOfStrongTrans (F := S1348K l)
      (S := S1419AffineOver (l := l))
      (T := S1419AffineOver (l := l))) h
  simpa [S1742HomOfStrongTrans_strongTransOfHom] using h'

/-- Exact missing strict round-trip on stack automorphisms: every StrongTrans
endomorphism of the representable stack is strictly the one induced by its
underlying scheme morphism, not only 2-isomorphic to it. -/
def S3120StrictRoundTripTarget : Prop :=
  forall eta : (S1536XF (l := l)).Hom (S1536XF (l := l)),
    eta = S1742StrongTransOfHom (F := S1348K l)
      (S1742HomOfStrongTrans (F := S1348K l)
        (S := S1419AffineOver (l := l))
        (T := S1419AffineOver (l := l)) eta)

/-- Exact missing uniqueness of square-one Over automorphisms of the S1419
representing scheme. -/
def S3120OverAutoUniqueTarget : Prop :=
  forall α : S1419AffineOver (l := l) ⟶ S1419AffineOver (l := l),
    α ≫ α = 𝟙 (S1419AffineOver (l := l)) ->
    α = S3119NegOverHom (l := l)

/-- Conditional field-5 uniqueness from the two exact bridges. -/
theorem S3120_field5_unique
    (hstrict : S3120StrictRoundTripTarget (l := l))
    (hunique : S3120OverAutoUniqueTarget (l := l))
    (inv : (S1536XF (l := l)).Hom (S1536XF (l := l)))
    (hsq : Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
      (Iut.HyperbolicOrbicurve.Hom.id (S1536XF (l := l)))) :
    inv = S3119NegEllipticInvolution (l := l) := by
  let α := S1742HomOfStrongTrans (F := S1348K l)
    (S := S1419AffineOver (l := l))
    (T := S1419AffineOver (l := l)) inv
  have hαsq : α ≫ α = 𝟙 (S1419AffineOver (l := l)) := by
    have hcongr := S1742HomOfStrongTrans_congr (F := S1348K l) hsq
    simpa [α, S1742HomOfStrongTrans_strongTransOfHom] using hcongr
  have hα : α = S3119NegOverHom (l := l) := hunique α hαsq
  calc
    inv = S1742StrongTransOfHom (F := S1348K l) α := hstrict inv
    _ = S1742StrongTransOfHom (F := S1348K l)
          (S3119NegOverHom (l := l)) := by rw [hα]
    _ = S3119NegEllipticInvolution (l := l) := rfl

#check S3120StrongTransOfHom_injective
#check S3120StrictRoundTripTarget
#check S3120OverAutoUniqueTarget
#check S3120_field5_unique

end LeanFormal.IUT.XiFPaper.S3120StackAutoFaithfulTarget
end