import tmp.sheaf.xif.paper.S2768FiveTorsionCardActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

noncomputable section
open WeierstrassCurve
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2769ProjAffineCardActual

open LeanFormal.IUT.XiFPaper.S2768FiveTorsionCardActual

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K] [IsAlgClosed K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- Projective-to-affine additive equivalence of the elliptic curve. -/
noncomputable def S2769ProjAffineEquiv :
    W.toProjective.Point ≃+ W.toProjective.toAffine.Point :=
  WeierstrassCurve.Projective.Point.toAffineAddEquiv W.toProjective

/-- The induced equivalence on `n`-torsion subgroups. -/
noncomputable def S2769ProjAffineTorsionEquiv (n : ℤ) :
    AddSubgroup.torsionBy W.toProjective.Point n ≃
      AddSubgroup.torsionBy W.toProjective.toAffine.Point n :=
  Equiv.subtypeEquiv (S2769ProjAffineEquiv W).toEquiv (by
    intro P
    change n • P = 0 ↔ n • (S2769ProjAffineEquiv W) P = 0
    constructor
    · intro h
      rw [← map_zsmul, h, map_zero]
    · intro h
      apply (S2769ProjAffineEquiv W).injective
      rw [map_zsmul, h, map_zero])

/-- Projective `5`-torsion has cardinality `25`, by transport from the affine
`25`-card theorem. -/
theorem S2769_projective_fiveTorsion_card :
    Nat.card (AddSubgroup.torsionBy W.toProjective.Point (5 : ℤ)) = 25 := by
  rw [Nat.card_congr (S2769ProjAffineTorsionEquiv W 5)]
  exact S2768_fiveTorsion_card W

/-- Affine and projective torsion cardinals agree. -/
theorem S2769_projAffine_torsion_card_eq (n : ℤ) :
    Nat.card (AddSubgroup.torsionBy W.toProjective.Point n) =
      Nat.card (AddSubgroup.torsionBy W.toProjective.toAffine.Point n) :=
  Nat.card_congr (S2769ProjAffineTorsionEquiv W n)

#check S2769ProjAffineEquiv
#check S2769ProjAffineTorsionEquiv
#check S2769_projective_fiveTorsion_card
#check S2769_projAffine_torsion_card_eq
#print axioms S2769_projective_fiveTorsion_card

end LeanFormal.IUT.XiFPaper.S2769ProjAffineCardActual
end
