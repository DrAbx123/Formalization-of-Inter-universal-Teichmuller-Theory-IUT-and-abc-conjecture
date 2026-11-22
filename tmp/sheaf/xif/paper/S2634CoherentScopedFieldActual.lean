import tmp.sheaf.xif.paper.S2625D6CoverCancellationData
import tmp.sheaf.xif.paper.S1852CoherentCoverActual

/-! # S2634: coherent-scoped cancellation wrapper (non-breaking) -/

noncomputable section
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S2619RightCancellationActual
open LeanFormal.IUT.XiFPaper.S2620M1CoherenceFields
open LeanFormal.IUT.XiFPaper.S2625D6CoverCancellationData

namespace LeanFormal.IUT.XiFPaper.S2634CoherentScopedFieldActual

universe u

/-- Per-coherent-cover cancellation data. -/
structure CoherentScopedCancellation (C : CoherentCover) where
  cancelRight : RightCancellation C.cover.map
  cancelWitness : M1RightCancellationWitness C.cover.map

/-- The scoped field: only coherent covers, not all S1728Cover. -/
def CoherentScopedField : Type 1 :=
  ∀ C : CoherentCover, CoherentScopedCancellation C

/-- Forget to the non-destructive D6 wrapper. -/
noncomputable def CoherentScopedCancellation.toD6
    {C : CoherentCover} (A : CoherentScopedCancellation C) :
    D6CoverWithCancellation C.cover where
  cancelRight := A.cancelRight
  cancelWitness := A.cancelWitness

/-- Cover-level consumer: presentation with finite-etale projection. -/
noncomputable def presentationOfCoherentScoped
    (F : CoherentScopedField) (C : CoherentCover)
    {X : EtaleStackOverField S1726K} (m : X.Hom C.cover.source)
    (T : SchemeOverField S1726K)
    (ptY : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T)
      C.cover.source.fiber)
    (Qy : EtaleStackBaseChangePresentation C.cover.map T
      (Pseudofunctor.StrongTrans.vcomp ptY C.cover.map))
    (Qx : EtaleStackBaseChangePresentation
      (Pseudofunctor.StrongTrans.vcomp m C.cover.map) T
      (Pseudofunctor.StrongTrans.vcomp ptY C.cover.map))
    (hQyF : AlgebraicGeometry.IsFinite Qy.projection.left)
    (hQyE : AlgebraicGeometry.Etale Qy.projection.left)
    (hQxF : AlgebraicGeometry.IsFinite Qx.projection.left)
    (hQxE : AlgebraicGeometry.Etale Qx.projection.left) :
    Σ' P : EtaleStackBaseChangePresentation m T ptY,
      AlgebraicGeometry.IsFinite P.projection.left ∧
        AlgebraicGeometry.Etale P.projection.left :=
  presentationOfCover (F C).toD6 m T ptY Qy Qx hQyF hQyE hQxF hQxE


/-- Coherent-scoped analogue of S2621's corrected field. -/
def CoherentScopedPresentationField : Type 1 :=
  ∀ (C : CoherentCover)
    {X : EtaleStackOverField S1726K} (m : X.Hom C.cover.source)
    (T : SchemeOverField S1726K)
    (ptY : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T)
      C.cover.source.fiber),
    (Qy : EtaleStackBaseChangePresentation C.cover.map T
      (Pseudofunctor.StrongTrans.vcomp ptY C.cover.map)) →
    (Qx : EtaleStackBaseChangePresentation
      (Pseudofunctor.StrongTrans.vcomp m C.cover.map) T
      (Pseudofunctor.StrongTrans.vcomp ptY C.cover.map)) →
    AlgebraicGeometry.IsFinite Qy.projection.left →
    AlgebraicGeometry.Etale Qy.projection.left →
    AlgebraicGeometry.IsFinite Qx.projection.left →
    AlgebraicGeometry.Etale Qx.projection.left →
    Σ' P : EtaleStackBaseChangePresentation m T ptY,
      AlgebraicGeometry.IsFinite P.projection.left ∧
        AlgebraicGeometry.Etale P.projection.left

noncomputable def coherentScopedPresentationField_of
    (F : CoherentScopedField) :
    CoherentScopedPresentationField :=
  fun C X m T ptY Qy Qx hQyF hQyE hQxF hQxE =>
    presentationOfCoherentScoped F C m T ptY Qy Qx
      hQyF hQyE hQxF hQxE

#check CoherentScopedPresentationField
#check coherentScopedPresentationField_of
#print axioms coherentScopedPresentationField_of

#check CoherentScopedField
#check presentationOfCoherentScoped
#print axioms presentationOfCoherentScoped

end LeanFormal.IUT.XiFPaper.S2634CoherentScopedFieldActual
end
