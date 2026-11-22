import tmp.sheaf.xif.paper.S2877UniqueReductionAudit
import tmp.sheaf.xif.paper.S2853E37NegationAutomorphismActual
import tmp.sheaf.xif.paper.S2858AlphaOverActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2877UniqueReductionAudit
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2856A6CoreWithInvolution
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2881OrderTwoClassificationAudit

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

/-!
## S2881: attempt at S2877OrderTwoAutClassification

What is available:
* S2853E37NegationAutomorphismActual constructs one nontrivial order-two
  chart-Z endomorphism S2853ChartZSchemeEndo, with ring hom S2853RingHom.
* S2858AlphaOverActual proves this chart endomorphism glues to
  globalAlphaScheme/alphaOver and that alphaOver squares to the identity.
* S2877 reduces the weakened uniqueness of stack involutions to
  S2877OrderTwoAutClassification:
  every beta with beta;beta = id is id or alphaOverS2844.

What is NOT available:
* no theorem classifies order-two scheme endomorphisms of the projective E37
  scheme.  S2853 gives one example, not an exhaustive list.
* no theorem relates an arbitrary endomorphism of the glued projective scheme
  to an affine coordinate-ring endomorphism of the chart-Z form
  (x,y) -> (x, -y-1).  A general scheme endomorphism need not preserve the
  chosen chart-Z, and even a chart-Z-preserving endomorphism can move the
  puncture.
* in fact, for the full projective elliptic curve E37, order-two
  automorphisms include translations by rational 2-torsion points
  (E37 has full rational 2-torsion: x=0, 1, -1).  These are not alphaOver.
  Therefore S2877OrderTwoAutClassification is not true for the full
  projective scheme without an extra origin/puncture-preservation
  hypothesis.  It can only be true for the punctured/origin-preserving
  orbicurve Hom type.

Exact missing objects:
1. A proof that the Hom type used in S2877 (endomorphisms of
   S2855HyperbolicOrbicurve) only contains automorphisms preserving the
   puncture/origin, not all scheme automorphisms of S2844X.
2. A classification theorem for order-two origin-preserving automorphisms
   of the E37 curve: id and the negation alphaOver.
3. A transport/coordinate computation identifying such an automorphism
   with the chart-Z substitution (x,y) -> (x,-y-1) and ruling out the
   translation 2-torsion cases under the puncture condition.

No classification is fabricated.  No fake order-two theorem.
-/

#check S2877OrderTwoAutClassification
#check S2877_unique_of_classification
#check S2853ChartZSchemeEndo
#check S2853RingHom
#check alphaOverS2844
#check alphaOverS2844_square

end LeanFormal.IUT.XiFPaper.S2881OrderTwoClassificationAudit
end
