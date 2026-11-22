import tmp.sheaf.xif.paper.S3128StrongBaseChangeFunctorActual
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Iut
open LeanFormal.IUT.XiFPaper.S3128QuotientSheafObjActual
open LeanFormal.IUT.XiFPaper.S3128StrongBaseChangeFunctorActual
namespace LeanFormal.IUT.XiFPaper.S3128PrestackMapIdActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F}
variable {U : SchemeOverField F}

noncomputable def S3128PrestackMapId :
    S3128StrongBaseChangeFunctor (F := F) (X := X) (𝟙 U) ≅
      𝟭 (S3128ZMod2QuotientSheafObj (F := F) (X := X) U) := by
  apply eqToIso
  dsimp [S3128StrongBaseChangeFunctor]
  rw [Over.mapId_eq]
  simp [Functor.op_id]

#check S3128PrestackMapId
end LeanFormal.IUT.XiFPaper.S3128PrestackMapIdActual