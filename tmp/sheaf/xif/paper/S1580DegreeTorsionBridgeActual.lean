import tmp.sheaf.xif.paper.S1431MulByIntDegreeActual
import tmp.sheaf.xif.paper.S1564GaussianTorsionBasisActual

/-! # S1580: S1431 degree -> point-kernel/LTorsion cardinality bridge: exact

S1431 proves `degree_mulByIntIsogeny`: a function-field embedding with the
`Φₙ/ΨSqₙ` coordinate condition and `IsCoprime (W.Φ n) (W.ΨSq n)` has
function-field degree `n^2`; in the separable case its separable degree is
`n^2`.

EXACT FIRST MISSING BRIDGES (none in tree):
1. actual function-field embedding f of [l] with S1431's coordinate condition
   and coprimality;
2. separability of the actual geometric [l] isogeny;
3. `#ker φ = deg φ` for a separable isogeny of elliptic curves;
4. identification of the point kernel with the projective algebraic-closure
   LTorsion/torsionBy carrier.

Only after 1-4 does S1431's degree n^2 give Nat.card LTorsion = n^2.
This file records the exact target; it assumes neither S1329 nor S1362 and
does not construct a fake point map or arbitrary basis.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1580DegreeTorsionBridgeActual

open LeanFormal.IUT

universe u
variable {F : Type u} [Field F]

/-- Exact target: actual l-torsion cardinality `l^2`. -/
def S1580LTorsionCardinalityExact
    (X : PuncturedEllipticCurve F) (l : PrimeGeFive) : Prop :=
  Nat.card (X.LTorsion l) = l.value ^ 2

end LeanFormal.IUT.XiFPaper.S1580DegreeTorsionBridgeActual

end
