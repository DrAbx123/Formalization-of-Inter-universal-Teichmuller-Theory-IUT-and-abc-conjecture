import Mathlib

namespace LeanFormal.IUT.XiFPaper.Node09ProductVolumeResidualActual

/-- Abstract conditional comparison: a singleton bound follows from a singleton
<= product comparison and a product <= weight bound.  This records the exact
paper-level decomposition; it does not construct either input. -/
theorem degreeBound_of_singleton_le_product_and_product_le_weight
    {singleton product weight eps D1 : Real}
    (h1 : singleton ≤ product)
    (h2 : product ≤ (1 + eps) * weight + D1) :
    singleton ≤ (1 + eps) * weight + D1 :=
  le_trans h1 h2

/-- Exact paper-level residual for hdegreeBound via P7 product volume. -/
def Node09ProductVolumeResidual : List String :=
  [ "P7 section 9.1/9.2 formalizes the q-ideal product-region volume V(J_q;C_q) = -sum_b n_b f_b log p_b (weighted M_q) for the global product of local ideals; it is not the value-monoid singleton volume of Node09SingletonPointCards",
    "to derive hdegreeBound one needs two comparisons: (1) the singleton volume of {scaleShift (logShellPoint a b c)} is at most the product-region volume; (2) the product-region volume is at most (1+eps)*arithmeticWeight + D1",
    "(1) requires the singleton to sit in the product region (a containment/membership comparison); (2) is the weighted q-ideal volume-to-arithmetic-weight estimate; neither comparison has a donor in the current tree",
    "no inhabitant is constructed; the abstract composition degreeBound_of_singleton_le_product_and_product_le_weight documents the exact missing shape" ]

end LeanFormal.IUT.XiFPaper.Node09ProductVolumeResidualActual
