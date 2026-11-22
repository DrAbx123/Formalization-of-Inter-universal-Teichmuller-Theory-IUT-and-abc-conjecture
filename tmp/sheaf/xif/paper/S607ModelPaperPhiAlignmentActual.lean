import tmp.sheaf.xif.paper.S547PhiCvPackageActual
import tmp.sheaf.xif.paper.S522QvPhiRamificationModelActual
import tmp.sheaf.xif.paper.S533QvPhiSubmonoidActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S607ModelPaperPhiAlignmentActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S533QvPhiSubmonoidActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S533QvPhiSubmonoidActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]

/-- The actual S522 model Phi. -/
abbrev s607ModelPhi (R : RamificationIndexData (K := K)) :
    DivisorialMonoidOn (Example32SmallBase K) (fun {_ _} f => IsIso f) :=
  qvPhiRamificationModel (K := K) R

/-- The actual N*qOrder split submonoid. -/
abbrev s607ModelSplit (qOrder : ℕ) : AddSubmonoid (ULift.{u+1} ℕ) :=
  qvOrderSubmonoid qOrder

/-- Exact minimal alignment theorem schema between the S522 model and paper
Phi_Cv / Phi_Cv^+ data.  The paper side is an explicit hypothesis: no paper
object is constructed here. -/
structure ModelPaperPhiAlignment
    (R : RamificationIndexData (K := K))
    (DvTri : Type (u+1)) [Category DvTri]
    (paperPhi : DivisorialMonoidOn.{u+1} DvTri (fun {_ _} _ => True))
    (paperSplit : (X : DvTri) → AddSubmonoid (paperPhi.obj X).carrier)
    (qOrder : ℕ)
    (paperQvImage : (X : DvTri) → (paperPhi.obj X).carrier) where
  baseEquiv : Example32SmallBase K ≌ DvTri
  phiObjEquiv : ∀ X : DvTri,
    ((s607ModelPhi R).obj (baseEquiv.inverse.obj X)).carrier ≃+ (paperPhi.obj X).carrier
  phiPullback_comm : ∀ {X Y : DvTri} (f : X ⟶ Y)
    (y : ((s607ModelPhi R).obj (baseEquiv.inverse.obj Y)).carrier),
    phiObjEquiv X ((s607ModelPhi R).pullback (baseEquiv.inverse.map f) y) =
      paperPhi.pullback f (phiObjEquiv Y y)
  split_eq : ∀ X : DvTri,
    AddSubmonoid.map (phiObjEquiv X).toAddMonoidHom
        (s607ModelSplit qOrder) = paperSplit X
  qvImage_eq : ∀ X : DvTri,
    paperQvImage X =
      phiObjEquiv X (ULift.up qOrder :
        ((s607ModelPhi R).obj (baseEquiv.inverse.obj X)).carrier)

/-- Exact minimal alignment obligation: no inhabitant is provided. -/
def ModelPaperPhiAlignmentRequired
    (R : RamificationIndexData (K := K))
    (DvTri : Type (u+1)) [Category DvTri]
    (paperPhi : DivisorialMonoidOn.{u+1} DvTri (fun {_ _} _ => True))
    (paperSplit : (X : DvTri) → AddSubmonoid (paperPhi.obj X).carrier)
    (qOrder : ℕ)
    (paperQvImage : (X : DvTri) → (paperPhi.obj X).carrier) : Prop :=
  Nonempty (ModelPaperPhiAlignment R DvTri paperPhi paperSplit qOrder paperQvImage)

end LeanFormal.IUT.XiFPaper.S607ModelPaperPhiAlignmentActual

end
