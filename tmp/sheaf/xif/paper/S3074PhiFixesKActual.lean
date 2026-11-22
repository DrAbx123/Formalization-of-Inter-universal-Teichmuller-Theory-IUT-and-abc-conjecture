import tmp.sheaf.xif.paper.S3073ChartZRestrictionActual
import tmp.sheaf.xif.paper.S2821E37ProjectiveOverActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3073ChartZRestrictionActual
open LeanFormal.IUT.XiFPaper.S3072ZSquareActual
open LeanFormal.IUT.XiFPaper.S3062ChartZPreservationProof
open LeanFormal.IUT.XiFPaper.S2821E37ProjectiveOverActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3074PhiFixesKActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

theorem S3074_zOver
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (hβ : β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X)
    (hfix : S3062InfinityFixed β)
    (D : S3073ChartZRestriction β) :
    D.z ≫ S2801E37StructureMap S3062ChartZPreservationProof.K =
      S2801E37StructureMap S3062ChartZPreservationProof.K := by
  have hβw : Over.Hom.left β ≫ (Over.hom S2844D6F6BaseChangeActual.S2844X) =
      (Over.hom S2844D6F6BaseChangeActual.S2844X) := by
    change Over.Hom.left β ≫ (Over.hom S2844D6F6BaseChangeActual.S2844X) =
      (Over.hom S2844D6F6BaseChangeActual.S2844X)
    exact Over.Hom.w β
  have h := congrArg (fun f => f ≫ S2821StructureMap S2844D6F6BaseChangeActual.K) D.hsquare
  calc D.z ≫ S2801E37StructureMap S3062ChartZPreservationProof.K
      = (D.z ≫ S2820E37ChartZMap S2844D6F6BaseChangeActual.K) ≫
          S2821StructureMap S2844D6F6BaseChangeActual.K := by
        rw [Category.assoc, S2821ChartZ_structure (K := S2844D6F6BaseChangeActual.K)]
    _ = (S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ Over.Hom.left β) ≫
          S2821StructureMap S2844D6F6BaseChangeActual.K := h.symm
    _ = S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫
          (Over.Hom.left β ≫ S2821StructureMap S2844D6F6BaseChangeActual.K) :=
        Category.assoc _ _ _
    _ = S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫
          S2821StructureMap S2844D6F6BaseChangeActual.K := by
        have hw := congrArg (fun f => S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ f) hβw
        exact hw
    _ = S2801E37StructureMap S3062ChartZPreservationProof.K :=
        S2821ChartZ_structure (K := S2844D6F6BaseChangeActual.K)

#check S3074_zOver
#print axioms S3074_zOver

end LeanFormal.IUT.XiFPaper.S3074PhiFixesKActual
end
