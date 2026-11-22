/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-!
# A726 lana umbrella import fix + pending-external audit (mainline)

Three lana files imported the bare umbrella module TateCurvesTheta (not resolvable:
the umbrella imports all submodules and the root module path is not a lake source root).
Their imports were replaced by the actual submodules used, keeping the mathematics
unchanged:

* Iut/Cor312/ThetaData/AdmissiblePrime.lean: import TateCurvesTheta -> import TateCurvesTheta.QParameter.JParametrization
  (it uses TateParameter.existsUnique_tateParameter_tateJ_eq);
* Iut/Cor312/ThetaData/TateStructure.lean: -> QParameter.Basic, TateCurve.TateUniformization, TateCurve.Parametrization;
* Iut/Cor312/ThetaData/TateIsomorphism.lean: -> QParameter.JParametrization, TateCurve.IntegralModel.

PadicLogVolume bare-import scan: none in the lana tree.

PENDING-EXTERNAL: the lana tree is not bulk-compiled; Mzk1LanaConsumerRowsActual
(rhs_le / localEstimate consumers) is written and ready, blocked only on lana oleans.
ABC gate NOT passed; no canonical change. -/

namespace Mzk1LanaUmbrellaImportFixActual

def importFixRows : List (String × String) :=
  [ ("AdmissiblePrime.lean", "TateCurvesTheta -> QParameter.JParametrization"),
    ("TateStructure.lean", "TateCurvesTheta -> QParameter.Basic + TateCurve.TateUniformization + TateCurve.Parametrization"),
    ("TateIsomorphism.lean", "TateCurvesTheta -> QParameter.JParametrization + TateCurve.IntegralModel"),
    ("PadicLogVolume bare imports", "none found in lana tree"),
    ("consumer file", "Mzk1LanaConsumerRowsActual written; waits for lana oleans"),
    ("scope", "math content unchanged; ABC gate NOT passed; no canonical change") ]

theorem importFixRows_length : importFixRows.length = 6 := rfl

end Mzk1LanaUmbrellaImportFixActual

/-! ### Axiom gates (top level) -/

#print axioms Mzk1LanaUmbrellaImportFixActual.importFixRows_length