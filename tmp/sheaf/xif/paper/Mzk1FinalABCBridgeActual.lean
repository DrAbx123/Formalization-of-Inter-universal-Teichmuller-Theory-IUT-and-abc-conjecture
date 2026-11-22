/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Iut.MainTheorem
import tmp.sheaf.xif.paper.Mzk1AbcDictionaryActual

/-!
# A743 final ABC bridge (mainline): LANA Iut.MainTheorem -> our ABCConjecture

`classicalABC_implies_ABCConjecture` transfers the LANA `Iut.ClassicalABC`
(nat radical, real exponent) to our `ABCConjecture` using the dictionary
`Mzk1AbcDictionaryActual`.

PENDING-EXTERNAL: `Iut.MainTheorem` needs the full Iut tree oleans; until then
this file cannot compile. No sorry/axiom; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1FinalABCBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1AbcDictionaryActual

/-- The LANA classical ABC conjecture implies our height/radical ABC statement. -/
theorem classicalABC_implies_ABCConjecture (h : Iut.ClassicalABC) : ABCConjecture := by
  apply abcBound_constant_pos
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨C, fun a b c habc => ?_⟩
  obtain ⟨ha, hb, hcop, hsum⟩ := (isABCTriple_iff_lana a b c).mp habc
  have key := hC a b c ha hb hcop hsum
  simpa [LeanFormal.IUT.radical, LeanFormal.IUT.natRadical] using key

/-- The Corollary 3.12 variant (LANA form) implies our ABC statement. -/
theorem abc_of_cor312VariantHolds (h : Iut.Cor312VariantHolds) : ABCConjecture :=
  classicalABC_implies_ABCConjecture (Iut.classicalABC_of_variant h)

/-- Pending-external status rows. -/
def bridgeRows : List (String × String) :=
  [ ("classicalABC -> ABCConjecture", "written via Mzk1AbcDictionaryActual"),
    ("cor312VariantHolds -> ABC", "written via Iut.classicalABC_of_variant"),
    ("pending external", "Iut.MainTheorem oleans not built yet; file ready"),
    ("scope", "ABC gate NOT passed; no canonical change") ]

theorem bridgeRows_length : bridgeRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1FinalABCBridgeActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1FinalABCBridgeActual.classicalABC_implies_ABCConjecture
#print axioms LeanFormal.IUT.XiFPaper.Mzk1FinalABCBridgeActual.abc_of_cor312VariantHolds
#print axioms LeanFormal.IUT.XiFPaper.Mzk1FinalABCBridgeActual.bridgeRows_length