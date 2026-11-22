import tmp.sheaf.xif.paper.S2496cFMapActual
import tmp.sheaf.xif.paper.S2482QiInvolutionActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiCurveActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
open LeanFormal.IUT.XiFPaper.S2495cFUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2496cFMapActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2497InvariantSchemeActual

/-- The x-coordinate is fixed by the elliptic involution: `phi ∘ inv = phi`. -/
theorem S2497phi_inv :
    S2482CoordinateRingInvolution.toRingHom.comp S2496phi = S2496phi := by
  ext x <;> simp [S2496phi, S2482CoordinateRingInvolution, S2482AffineInvolutionAlgHom]

/-- At the scheme level, the x-coordinate quotient map is invariant under the
elliptic involution. -/
theorem S2497InvScheme :
    S2482AffineInvolution ≫ S2496f = S2496f := by
  apply CategoryTheory.Over.OverMorphism.ext
  dsimp [S2482AffineInvolution, S2496f]
  rw [← Spec.map_comp, Spec.map_inj]
  change CommRingCat.ofHom
    (S2482CoordinateRingInvolution.toRingHom.comp S2496phi) =
      CommRingCat.ofHom S2496phi
  rw [S2497phi_inv]

#print axioms S2497phi_inv
#print axioms S2497InvScheme

end LeanFormal.IUT.XiFPaper.S2497InvariantSchemeActual
end