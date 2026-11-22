import tmp.sheaf.xif.paper.S2482QiInvolutionSquareActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2482InvolutionUniquenessAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionSquareActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open CategoryTheory

noncomputable def S2482IdentityTwoIso :
    Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp
        (Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve)
        (Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve))
      (Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve) := by
  change Iso
    (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.id (S1742YS (F := F) S2482AffineOver))
      (Pseudofunctor.StrongTrans.id (S1742YS (F := F) S2482AffineOver)))
    (Pseudofunctor.StrongTrans.id (S1742YS (F := F) S2482AffineOver))
  exact Iso.refl _

theorem S2482_unique_elliptic_involution_forces_identity
    (elliptic : S2482Orbicurve.Hom S2482Orbicurve)
    (huniq : ∀ inv : S2482Orbicurve.Hom S2482Orbicurve,
      Iut.HyperbolicOrbicurve.Hom.TwoIso
        (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
        (Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve) →
      inv = elliptic) :
    elliptic = Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve := by
  have h := huniq (Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve)
    S2482IdentityTwoIso
  exact h.symm

def S2482CorrectedEllipticUniqueness
    (elliptic : S2482Orbicurve.Hom S2482Orbicurve) : Prop :=
  ∀ inv : S2482Orbicurve.Hom S2482Orbicurve,
    Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
      (Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve) →
    inv ≠ Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve →
    Nonempty (Iut.HyperbolicOrbicurve.Hom.TwoIso inv elliptic)

/-- Source structure should add this nontriviality field alongside the
uniqueness field; without it uniqueness forces the identity (S2482IdentityTwoIso). -/
def S2482EllipticInvolutionNontrivial : Prop :=
  S2482EllipticInvolution ≠ Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve

end LeanFormal.IUT.XiFPaper.S2482InvolutionUniquenessAuditActual

end