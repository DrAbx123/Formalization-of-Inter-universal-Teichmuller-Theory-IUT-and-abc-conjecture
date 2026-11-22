import tmp.sheaf.xif.paper.S2858AlphaOverActual
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2875UniqueInvolutionActual
open Iut
variable {F : Type u} [Field F]
variable (X : Iut.HyperbolicOrbicurve F)

noncomputable def identityTwoIso :
    Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp
        (Iut.HyperbolicOrbicurve.Hom.id X)
        (Iut.HyperbolicOrbicurve.Hom.id X))
      (Iut.HyperbolicOrbicurve.Hom.id X) := by
  exact (ρ_ (show X.stack.fiber ⟶ X.stack.fiber from
    Pseudofunctor.StrongTrans.id X.stack.fiber))

theorem unique_elliptic_involution_forces_identity
    (elliptic : X.Hom X)
    (huniq : ∀ inv : X.Hom X,
      Iut.HyperbolicOrbicurve.Hom.TwoIso
        (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
        (Iut.HyperbolicOrbicurve.Hom.id X) →
      inv = elliptic) :
    elliptic = Iut.HyperbolicOrbicurve.Hom.id X := by
  have h := huniq (Iut.HyperbolicOrbicurve.Hom.id X)
    (identityTwoIso X)
  exact h.symm

#check unique_elliptic_involution_forces_identity
#print axioms unique_elliptic_involution_forces_identity
end LeanFormal.IUT.XiFPaper.S2875UniqueInvolutionActual
