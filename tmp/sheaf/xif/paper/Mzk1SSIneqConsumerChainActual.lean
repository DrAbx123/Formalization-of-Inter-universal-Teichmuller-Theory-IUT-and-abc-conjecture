/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Iut.WallEquiv.Basic
import tmp.sheaf.xif.paper.Mzk1AbcDictionaryActual
import tmp.sheaf.xif.paper.Mzk1FinalABCBridgeActual

/-!
# A809 SSIneq consumer chain (mainline)

`abcConjecture_of_forall_ssIneq` : the Scholze–Stix inequality for all initial
Θ-data implies `ABCConjecture`, through lana's `Iut.WallEquiv.classicalABC_of_ss`
and our dictionary bridge `Mzk1FinalABCBridgeActual.classicalABC_implies_ABCConjecture`.

PENDING-EXTERNAL: needs the lana `Iut` oleans (`Iut/WallEquiv/Basic` etc. are being
compiled by the DAG watchdog). No axiom; no sorry; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1SSIneqConsumerChainActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1FinalABCBridgeActual

/-- (SS) for every initial Θ-data implies ABC. -/
theorem abcConjecture_of_forall_ssIneq
    (h : ∀ D : Iut.InitialThetaData.{0}, Iut.Wall.SSIneq D) :
    ABCConjecture :=
  classicalABC_implies_ABCConjecture (Iut.WallEquiv.classicalABC_of_ss h).2.2

/-- Variant-level form of the same chain. -/
theorem cor312VariantHolds_of_forall_ssIneq
    (h : ∀ D : Iut.InitialThetaData.{0}, Iut.Wall.SSIneq D) :
    Iut.Cor312VariantHolds :=
  (Iut.WallEquiv.classicalABC_of_ss h).1

/-- Pending-external status rows. -/
def consumerRows : List (String × String) :=
  [ ("input", "forall D, Iut.Wall.SSIneq D"),
    ("lana consumer", "Iut.WallEquiv.classicalABC_of_ss (Basic.lean:180)"),
    ("dictionary", "Mzk1FinalABCBridgeActual.classicalABC_implies_ABCConjecture"),
    ("output", "LeanFormal.IUT.ABCConjecture"),
    ("scope", "ABC gate NOT passed; no canonical change") ]

theorem consumerRows_length : consumerRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1SSIneqConsumerChainActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1SSIneqConsumerChainActual.abcConjecture_of_forall_ssIneq
#print axioms LeanFormal.IUT.XiFPaper.Mzk1SSIneqConsumerChainActual.cor312VariantHolds_of_forall_ssIneq
#print axioms LeanFormal.IUT.XiFPaper.Mzk1SSIneqConsumerChainActual.consumerRows_length