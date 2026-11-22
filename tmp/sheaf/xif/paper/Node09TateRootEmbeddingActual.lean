import LeanFormal.IUT.Foundations.Geometry.TateFiniteParameterField
import LeanFormal.IUT.Foundations.PAdicAnalytic.TateInverseJFinal

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.Node09TateRootEmbeddingActual

def Node09TateRootEmbeddingStatus : List String :=
  [ "available: TateFiniteParameterField provides the finite parameter field and no-pole descent; TateInverseJFinal gives the actual q with |q|=|t|",
    "missing: the root-field volume formula (R) needs the actual root extension L/F, the normalized volume V_L(alpha O_L; O_L), and the comparison of normalization factors; these objects are not constructed in the tree",
    "planned shape (IUT III §5.3): for a root field L/F of degree r, (1/r) * V_L(alpha O_L;O_L) = (1/(2l)) * log|q|_mod,F; the root alpha^(2l)=q comes from the actual 2l-torsion rationality",
    "no fake, no True/PUnit/axiom/sorry; no numeric identity is assumed" ]

end LeanFormal.IUT.XiFPaper.Node09TateRootEmbeddingActual