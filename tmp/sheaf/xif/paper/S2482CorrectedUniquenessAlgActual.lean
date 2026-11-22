import tmp.sheaf.xif.paper.S2482OrderTwoAlgAutClassificationAltActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S2482CorrectedUniquenessAlgActual

open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2482QiNontrivialActual
open LeanFormal.IUT.XiFPaper.S2482OrderTwoAlgAutClassificationAltActual

theorem S2482_corrected_uniqueness_alg
    (φ : S2482CoordinateRing ≃ₐ[F] S2482CoordinateRing)
    (hφ : φ.toAlgHom.comp φ.toAlgHom = AlgHom.id F S2482CoordinateRing)
    (hne : φ ≠ AlgHom.id F S2482CoordinateRing) :
    φ.toAlgHom = S2482CoordinateRingInvolution := by
  rcases S2482OrderTwoAlgAutClassification_actual φ hφ with h | h
  · exact absurd h hne
  · exact h


end LeanFormal.IUT.XiFPaper.S2482CorrectedUniquenessAlgActual
end