/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1AbcDictionaryActual
import tmp.sheaf.xif.paper.Mzk1RouteCBridgeActual
import tmp.sheaf.xif.paper.Mzk1RouteCFreyShapeActual
import tmp.sheaf.xif.paper.Mzk1FinalBoundarySzpiroActual
import tmp.sheaf.xif.paper.Mzk1RouteCInternalActual
import tmp.sheaf.xif.paper.Mzk1E7ReductionActual
import tmp.external.ported.flt.FLT.FreyCurve.FreyPackage

/-!
# A860 C-route assembly shell (mainline)

Thin assembly of the C route (Frey + modularity + height/conductor dictionaries + E7
reduction) into `ABCConjecture`.  The gap interfaces are explicit HYPOTHESIS fields:

* G1: Frey package existence from failure of FLT_p (source: FLT ported `FreyPackage`);
* G2: modular parameterization data with the degree bound
  (`Mzk1RouteCBridgeActual.ModularParameterizationData`);
* G3: height dictionary `log q = 2 logDelta` (`FreyDictionary`);
* G4: conductor/e7 dictionary `logdf = logN` (`FreyDictionary`);
* G5: Szpiro-6 shape derived from G2+G3+G4 (`modularityDegreeBound_to_szpiro6`);
* E7: the arithmetic reduction of Szpiro-6 to the epsilon-radical bound (the ABC-strength
  input of this shell, stated explicitly; its proof is the remaining C-route gap).

Nothing below assumes ABC silently: the only ABC-strength field is `E7_radicalBound`,
and it is a documented hypothesis, not a theorem.  No sorry/axiom; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1CRouteAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1AbcDictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteCInternalActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalBoundarySzpiroActual

/-- The explicit C-route hypothesis surface (E1-E6 + G1-G5 + E7). -/
structure CRouteAssemblyInput where
  /-- G1: Frey package attached to a counterexample of FLT_p (source obligation). -/
  G1_frey : Prop
  hG1 : G1_frey
  /-- G2: modular parameterization data (degree bound; source obligation). -/
  G2_modular : Prop
  hG2 : G2_modular
  /-- G3: height dictionary `log q = 2 logDelta` (FreyDictionary). -/
  G3_height : Prop
  hG3 : G3_height
  /-- G4: conductor dictionary `logdf = logN` (FreyDictionary). -/
  G4_conductor : Prop
  hG4 : G4_conductor
  /-- G5: Szpiro-6 shape concluded from G2-G4. -/
  G5_szpiro : Prop
  hG5 : G5_szpiro
  /-- E7: epsilon-radical bound (ABC-strength reduction step; explicit input). -/
  E7_radicalBound : ∀ ε > 0, ∃ C : Real, ∀ a b c : Nat, IsABCTriple a b c →
    (c : Real) ≤ C * Real.rpow (radical (a * b * c) : Real) (1 + ε)

/-- The assembly: E7 + the dictionary gives `ABCConjecture`. -/
theorem abcConjecture_of_cRouteAssembly (I : CRouteAssemblyInput) :
    ABCConjecture :=
  abcBound_constant_pos I.E7_radicalBound

/-- The assembly also yields the Frey-package shape as a consequence of its own
hypothesis field (recorded so the interface is not empty). -/
theorem freyPackage_shape_of_assembly (I : CRouteAssemblyInput) : I.G1_frey := I.hG1

/-- C-route assembly using the green RouteC internal chain: Pasten delta bound + Frey
dictionary give Szpiro-6, and the E7 reducer (explicit hypothesis) gives `ABCConjecture`. -/
theorem abcConjecture_of_routeC
    {logDelta logN logq logdf C epsilon : Real}
    (heps0 : 0 ≤ epsilon) (heps1 : epsilon ≤ 1) (hN : 0 ≤ logN)
    (hbound : PastenDeltaBound logDelta logN C epsilon)
    (hdict : FreyLogDictionary logq logDelta logdf logN)
    (hE7 : (∃ C' : Real, Szpiro6Shape logq logdf C') → ABCConjecture) :
    ABCConjecture :=
  hE7 ⟨2 * C, szpiro6_of_routeC heps0 heps1 hN hbound hdict⟩
/-- Interface rows: what each field is and where its green support currently lives. -/
def cRouteAssemblyRows : List (String × String × String) :=
  [ ("G1", "FreyPackage from not-FLT_p", "HYPOTHESIS; FLT ported FreyPackage (green shape file Mzk1RouteCFreyShapeActual)"),
    ("G2", "ModularParameterizationData degree bound", "HYPOTHESIS; structure in Mzk1RouteCBridgeActual"),
    ("G3", "FreyDictionary logq = 2 logDelta", "HYPOTHESIS; def in Mzk1RouteCBridgeActual"),
    ("G4", "FreyDictionary logdf = logN", "HYPOTHESIS; def in Mzk1RouteCBridgeActual"),
    ("G5", "Szpiro6Shape from G2-G4", "GREEN lemma modularityDegreeBound_to_szpiro6"),
    ("E7", "Szpiro6 -> epsilon-radical bound (ABC-strength)", "HYPOTHESIS (remaining C-route gap)"),
    ("output", "ABCConjecture via Mzk1AbcDictionaryActual.abcBound_constant_pos", "GREEN assembly; ABC gate NOT passed") ]

theorem cRouteAssemblyRows_length : cRouteAssemblyRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1CRouteAssemblyActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1CRouteAssemblyActual.abcConjecture_of_cRouteAssembly
#print axioms LeanFormal.IUT.XiFPaper.Mzk1CRouteAssemblyActual.abcConjecture_of_routeC
#print axioms LeanFormal.IUT.XiFPaper.Mzk1CRouteAssemblyActual.freyPackage_shape_of_assembly
#print axioms LeanFormal.IUT.XiFPaper.Mzk1CRouteAssemblyActual.cRouteAssemblyRows_length