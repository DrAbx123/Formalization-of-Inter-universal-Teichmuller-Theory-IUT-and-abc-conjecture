import tmp.sheaf.xif.paper.S2094FullUniversalInputsActual
noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
namespace Test2097
universe u
example {W A B : EtaleStackPseudofunctor S1726K} {f g : Pseudofunctor.StrongTrans W A}
    (al be : f ⟶ g) {u u' : Pseudofunctor.StrongTrans A B} (e : Iso u u')
    (h : Pseudofunctor.StrongTrans.whiskerRight al u = Pseudofunctor.StrongTrans.whiskerRight be u) :
    Pseudofunctor.StrongTrans.whiskerRight al u' = Pseudofunctor.StrongTrans.whiskerRight be u' := by
  change al ▷ u = be ▷ u at h
  change al ▷ u' = be ▷ u'
  exact LeanFormal.IUT.XiFPaper.S2071PastingWitnessActual.Coherence.S2071WhiskerRight_base_iso e h
end Test2097
end