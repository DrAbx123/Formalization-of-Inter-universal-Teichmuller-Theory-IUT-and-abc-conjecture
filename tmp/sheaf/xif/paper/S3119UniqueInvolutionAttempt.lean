import tmp.sheaf.xif.paper.S3119NegInvolutionOverActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import tmp.sheaf.xif.paper.S1742HomVcompActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped SpecOfNotation
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionOverActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual

namespace LeanFormal.IUT.XiFPaper.S3119UniqueInvolutionAttempt

variable {l : PrimeGeFive}

/-- The exact field-5 target: uniqueness of the order-two involution. -/
def S3119UniqueEllipticInvolutionTarget : Prop :=
  ∀ inv : (S1536XF (l := l)).Hom (S1536XF (l := l)),
    Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
      (Iut.HyperbolicOrbicurve.Hom.id (S1536XF (l := l))) →
    inv = S3119NegEllipticInvolution (l := l)

/-- The 2-Yoneda bridge from a stack self-morphism to an Over self-morphism. -/
noncomputable def S3119OverHomOfStackInv
    (inv : (S1536XF (l := l)).Hom (S1536XF (l := l))) :
    S1419AffineOver l ⟶ S1419AffineOver l :=
  S1742HomOfStrongTrans (F := S1348K l) inv

#check S1742HomOfStrongTrans
#check S1742StrongTransOfHom
#check S1742StrongTransIsoOfHom
#check S1742HomOfStrongTrans_strongTransOfHom
#check S1742Key
#check Spec.map_surjective
#check Spec.map_injective
#check Spec.map_eq_id

/-- `S1742StrongTransOfHom` is injective: it has a left inverse
`S1742HomOfStrongTrans`. -/
theorem S3119StrongTransOfHom_injective (F : Type) [Field F]
    {S T : Iut.SchemeOverField F} :
    Function.Injective
      (fun f : S ⟶ T => S1742StrongTransOfHom (F := F) f) := by
  intro f g h
  have h' := congrArg (S1742HomOfStrongTrans (F := F)) h
  simpa only [S1742HomOfStrongTrans_strongTransOfHom] using h'

/-- The missing converse bridge: equality of underlying Over morphisms
determines equality of the corresponding strong transformations.  S1742 only
supplies a 2-isomorphism `S1742StrongTransOfHom (S1742HomOfStrongTrans eta)`
with `eta`. -/
def S3119StrongTrans_eq_of_hom_eq_target (F : Type) [Field F]
    {S T : Iut.SchemeOverField F} : Prop :=
  ∀ eta theta : Pseudofunctor.StrongTrans (S1742YS (F := F) S)
      (S1742YS (F := F) T),
    S1742HomOfStrongTrans (F := F) eta =
      S1742HomOfStrongTrans (F := F) theta → eta = theta


theorem S3119StrongTrans_eq_of_hom_eq (F : Type) [Field F]
    {S T : Iut.SchemeOverField F}
    (eta theta : Pseudofunctor.StrongTrans (S1742YS (F := F) S)
      (S1742YS (F := F) T))
    (h : S1742HomOfStrongTrans (F := F) eta =
      S1742HomOfStrongTrans (F := F) theta) : eta = theta := by
  have happ : ∀ a, eta.app a = theta.app a := by
    intro a
    rw [← S1742AppEq eta a, ← S1742AppEq theta a, h]
  cases eta with
  | mk app nat nn ni nc =>
  cases theta with
  | mk app' nat' nn' ni' nc' =>
  simp only at happ
  congr with a b f
  exact Subsingleton.elim _ _

#check S3119StrongTrans_eq_of_hom_eq
#print axioms S3119StrongTrans_eq_of_hom_eq

#check S3119StrongTransOfHom_injective
#check S3119StrongTrans_eq_of_hom_eq_target
#print axioms S3119StrongTransOfHom_injective

#check S3119UniqueEllipticInvolutionTarget
#check S3119OverHomOfStackInv

end LeanFormal.IUT.XiFPaper.S3119UniqueInvolutionAttempt
end
