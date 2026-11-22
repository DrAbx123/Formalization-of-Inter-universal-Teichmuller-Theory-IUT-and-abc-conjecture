import tmp.sheaf.xif.paper.S1348D6OrbicurveActual

/-! # S1381: connected degree-2 cover — exact boundary

S1348 uses the split finite etale K-algebra `L = K × K` and the K-points of
`R ⊗_K L` as `SourceOrbicurveClause.cover`; its cover map is surjective and
nondegenerate.  `L` is disconnected.

A connected degree-2 cover would use a quadratic field `L = K(√d)` with `d`
nonsquare in `K = Q(i)` (e.g. d = 5 or 2).  The algebra `K(√d)` is finite
etale over K, but its base change `R ⊗_K L` has **no K-algebra section**
`L → K` (a nonsplit quadratic field does not embed in K).  Consequently the
K-points of `Spec(R ⊗_K L)` are empty, so the same point-set `cover` carrier
with `coverToPunctured` cannot be surjective onto the nonempty punctured
K-points.  Replacing the split cover by the connected algebra therefore cannot
produce the S1348/SourceOrbicurveClause cover on K-points.

Exact first field: a connected finite-etale cover carrier that is not the
K-point set of a nonsplit quadratic algebra, together with a surjective
K-point realization to the punctured curve.  Equivalently, the cover field
must be a scheme/stack (or an L-point carrier with a K-point projection), and
the nonempty/surjective point realization must be constructed.  No such actual
map exists in the tree; terminal/PUnit/split substitutes are not used.

The concrete nonsquare certificate for d=5 or 2 in `GaussianField` is also not
available in the tree; it would be needed before even the connected algebra
`K(√d)` could be certified.  This file records the boundary only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1381ConnectedCoverActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual

#check S1348FiniteEtaleAlgebra
#check S1348Cover
#check S1348CoverToPunctured
#check S1348CoverToPunctured_surjective
#check S1348CoverToPunctured_not_injective

end LeanFormal.IUT.XiFPaper.S1381ConnectedCoverActual
end
