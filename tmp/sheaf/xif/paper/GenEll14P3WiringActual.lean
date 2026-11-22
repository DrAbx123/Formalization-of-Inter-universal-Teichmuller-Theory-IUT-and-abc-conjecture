import tmp.sheaf.xif.paper.GenEll09IUTIVSection2ConsumerActual
import tmp.sheaf.xif.paper.GenEll05bChainWiringActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# GenEll14: P3 consumer wired to mainline's Theorem 2.1 (ii)=>(i) 11-row chain wiring

Mainline landed GenEll05bChainWiringActual (GenEll05bWiringMap: 11-row wiring map for
the Theorem 2.1 (ii)=>(i) inputs, results EXIT=0 3096).  This file consumes that
wiring map in the P3 consumer (GenEll09IUTIVSection2ConsumerActual): the rows are the
explicit named inputs the conditional Cor 2.3 theorem expects.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.GenEll14P3WiringActual

open LeanFormal.IUT.XiFPaper.GenEll05bChainWiringActual
open LeanFormal.IUT.XiFPaper.GenEll05Theorem21Actual
open LeanFormal.IUT.XiFPaper.GenEll09IUTIVSection2ConsumerActual

/-- The 11-row wiring map reused as the explicit input list of the P3 consumer. -/
abbrev genEllP3WiringRows : List (String × String × String) := GenEll05bWiringMap

/-- The wiring map has 11 rows (reused mainline count). -/
theorem genEllP3WiringRows_length : genEllP3WiringRows.length = 11 :=
  GenEll05bWiringMap_length

/-- A P3 consumer bundle: the conditional Cor 2.3 theorem together with the exact
11 named wiring inputs it consumes. -/
structure GenEllP3ConsumerBundle where
  /-- the explicit Theorem 2.1 (ii)=>(i) input wiring -/
  wiring : List (String × String × String)
  /-- the conditional Cor 2.3 statement (consumer shape) -/
  cor23 : ∀ {X : Type} (K : Set X) (ht logDiff logCond : X → Real) (eps : Real),
    CaseII K ht logDiff logCond eps →
      (CaseII K ht logDiff logCond eps → CaseI ht logDiff logCond eps) →
        CaseI ht logDiff logCond eps

/-- The P3 consumer bundle is constructible: mainline's wiring plus GenEll09's
conditional Cor 2.3 theorem. -/
def genEllP3ConsumerBundle : GenEllP3ConsumerBundle where
  wiring := genEllP3WiringRows
  cor23 := fun K ht logDiff logCond eps hCaseII hIItoI =>
    iutIVSection2_cor23_bdClass (K := K) ht logDiff logCond eps hCaseII hIItoI

/-- The bundle's wiring is exactly mainline's 11-row map. -/
theorem genEllP3ConsumerBundle_wiring :
    genEllP3ConsumerBundle.wiring = GenEll05bWiringMap :=
  rfl

/-- The bundle's conditional consumer is the GenEll09 Cor 2.3 theorem. -/
theorem genEllP3ConsumerBundle_cor23
    {X : Type} (K : Set X) (ht logDiff logCond : X → Real) (eps : Real)
    (hCaseII : CaseII K ht logDiff logCond eps)
    (hIItoI : CaseII K ht logDiff logCond eps → CaseI ht logDiff logCond eps) :
    CaseI ht logDiff logCond eps :=
  genEllP3ConsumerBundle.cor23 K ht logDiff logCond eps hCaseII hIItoI

end LeanFormal.IUT.XiFPaper.GenEll14P3WiringActual

end
