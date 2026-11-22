import tmp.sheaf.xif.paper.S2027LocalArtinActual
import tmp.sheaf.xif.paper.S2089FiniteAbelianSubextensionActual
import Reciprocity.ProfiniteCompletion
noncomputable section
set_option maxHeartbeats 2000000
namespace LeanFormal.IUT.XiFPaper.S2093ArtinM2aBridge
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2089FiniteAbelianSubextensionActual
variable {p : Nat} [Fact (Nat.Prime p)]
variable (U : LeanFormal.IUT.XiFPaper.S2017VerlagerungActual.Index p)
local notation "E" => localField p U
local notation "Ω" => AlgebraicClosure ℚ_[p]
/-- Artin retyped to the S2027 max abelian extension. -/
noncomputable def artinRetyped :
    (localField p U)ˣ →* Gal(↥(maximalAbelianExtension p U) / localField p U) :=
  (galoisGroupEquiv U).toMonoidHom.comp (PadicField.artin p (localField p U) (AlgebraicClosure ℚ_[p]))
/-- M2a-core: the profinite completion of L^x is isomorphic to Gal(L^ab/L). -/
noncomputable def localReciprocityIsomorphism :
    unitProfiniteCompletion p U ≃* Gal(↥(maximalAbelianExtension p U) / localField p U) :=
  (PadicField.artinCompletionEquiv p (localField p U) (AlgebraicClosure ℚ_[p])).toMulEquiv.trans (galoisGroupEquiv U)
#print axioms artinRetyped
#print axioms localReciprocityIsomorphism
end LeanFormal.IUT.XiFPaper.S2093ArtinM2aBridge
end
