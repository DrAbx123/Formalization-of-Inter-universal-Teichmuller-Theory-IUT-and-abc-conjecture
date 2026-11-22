import tmp.sheaf.xif.paper.S1598PolyToFieldCCActual
import tmp.sheaf.xif.paper.S1491NormEDSNetActual
noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
namespace WeierstrassCurve.Universal
theorem s1599IsEllipticNet_psi_comm {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) : IsEllipticNet W.ψ := by
  rw [show W.ψ = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) from rfl]
  exact IsEllipticNet.normEDS _ _ _
theorem s1599IsEllipticNet_ψᵤ : IsEllipticNet (fun k : ℤ => ψᵤ k) :=
  (s1599IsEllipticNet_psi_comm (R := MvPolynomial Coeff ℤ) curve).comp polyToField
def S1599SmulXSubSmulX : Prop :=
  ∀ m n : ℤ, m ≠ 0 → n ≠ 0 →
    smulX m - smulX n =
      ψᵤ (n + m) * ψᵤ (n - m) / (ψᵤ n * ψᵤ m) ^ 2
-- Exact first missing for the TauCeti proof: the relator normal form differs
-- from the old EllSequence.net API.  `isEllipticSequence n m 1` unfolds to
-- IsEllipticNet.rel with four indices; the conversion below leaves the
-- cross-term identity ψᵤ(n+m)ψᵤ(n-m) = -rel ψᵤ n m 1 0 unresolved.
end WeierstrassCurve.Universal
end
