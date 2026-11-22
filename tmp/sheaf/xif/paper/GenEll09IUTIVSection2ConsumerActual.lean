import LeanFormal.IUT.IUTIV.Estimates.Section2
import tmp.sheaf.xif.paper.GenEll01BasicActual
import tmp.sheaf.xif.paper.GenEll05Theorem21Actual
import tmp.sheaf.xif.paper.GenEll08MainReductionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# GenEll09: P3 integration — IUT IV §2 consumer (replaces the [machine-gap] citation layer)

Plan coord/GENELL-FORMALIZATION-PLAN.md §P3.  The IUT IV §2 file
LeanFormal/IUT/IUTIV/Estimates/Section2.lean is a statement/card file whose
[machine-gap] cites "[GenEll] Thm 2.1 equivalence reduction".  This file replaces
that citation with the EXPLICIT CONDITIONAL THEOREM: given

* the IUT Thm 1.10 + Cor 2.2 output in GenEll form (BD-class inequality on the
  compactly-bounded subset K: CaseII K ht logDiff logCond eps), and
* the GenEll Theorem 2.1 (ii)=>(i) direction as an exact named paper input
  (Theorem21_ii_implies_i_required, GenEll05Theorem21Actual:50), while
  (i)=>(ii) is PROVED (theorem21_i_implies_ii:32),

the §2 Cor 2.3 BD-class inequality on the general curve follows
(CaseI ht logDiff logCond eps).  At the ABC level the GenEll08 main-reduction
consumer interface yields ABC for all hyperbolic curves from ABC for the
general-position/compactly-bounded family.

HONESTY: this is P3 integration, not a new deep proof.  The deep inputs
([Mzk1] noncritical Belyi existence, Thm 3.8, Cor 4.3/4.4) stay exact named
paper-inputs; the Section2 [machine-gap] is now an explicit conditional theorem
with those named inputs, never an assumed axiom.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.GenEll09IUTIVSection2ConsumerActual

universe u

open LeanFormal.IUT.XiFPaper.GenEll01BasicActual
open LeanFormal.IUT.XiFPaper.GenEll05Theorem21Actual
open LeanFormal.IUT.XiFPaper.GenEll08MainReductionActual

/-- The Section2 card this consumer replaces (id is definitional). -/
theorem section2_card_id :
    LeanFormal.IUT.Audit.iutIVSection2.id = "IUT-IV.section-2" := rfl

/-- GenEll Theorem 2.1 as an explicit equivalence, conditional on the paper-input
direction (ii)=>(i): (i)=>(ii) is proved (GenEll05Theorem21Actual:32). -/
theorem theorem21_equiv_of_paperInput
    {X : Type u} (K : Set X) (ht logDiff logCond : X → Real) (eps : Real)
    (hIItoI : CaseII K ht logDiff logCond eps → CaseI ht logDiff logCond eps) :
    CaseI ht logDiff logCond eps ↔ CaseII K ht logDiff logCond eps :=
  ⟨fun h => theorem21_i_implies_ii K ht logDiff logCond eps h, hIItoI⟩

/-- **IUT IV §2 consumer (explicit conditional Cor 2.3):** the IUT Thm 1.10 + Cor 2.2
BD-class output on the compactly-bounded subset plus GenEll Theorem 2.1 (ii)=>(i)
gives the general BD-class inequality — the §2 [machine-gap] replaced by an explicit
theorem with named inputs. -/
theorem iutIVSection2_cor23_bdClass
    {X : Type u} (K : Set X) (ht logDiff logCond : X → Real) (eps : Real)
    (thm110Cor22CaseII : CaseII K ht logDiff logCond eps)
    (genEllIItoI : CaseII K ht logDiff logCond eps → CaseI ht logDiff logCond eps) :
    CaseI ht logDiff logCond eps :=
  genEllIItoI thm110Cor22CaseII

/-- **ABC-level P3 consumer:** with the GenEll main-reduction statement shape
(Thm 2.1 equivalence + §3 Thm 3.8 + §4 Cor 4.3/4.4) and ABC for the general-position
family, ABC for all hyperbolic curves follows.  This is the explicit conditional
form intended for the IUT IV §2 / Cor 2.3 consumer interface. -/
theorem iutIVSection2_abcAll_of_genEllMainReduction
    {theorem21Equiv theorem38 cor43 cor44 abcAll abcGeneralPosition : Prop}
    (hMain : GenEllMainReductionStatement theorem21Equiv theorem38 cor43 cor44
      abcAll abcGeneralPosition)
    (h21 : theorem21Equiv) (h38 : theorem38) (h43 : cor43) (h44 : cor44)
    (hGP : abcGeneralPosition) :
    abcAll :=
  (genEll_mainReduction_shape hMain h21 h38 h43 h44).mp hGP

/-- The exact remaining paper-inputs of the §2 replacement (class B; explicit names). -/
def iutIVSection2RemainingPaperInputs : List (String × String) :=
  [ ("Thm 2.1 (ii)=>(i)", "GenEll05Theorem21Actual.Theorem21_ii_implies_i_required (paper-input)"),
    ("[Mzk1] noncritical Belyi", "GenEll05Theorem21Actual.Theorem21ReductionInputs.noncriticalBelyiExists (paper-input; corpus Noncritical Belyi Maps)"),
    ("§3 Thm 3.8", "GenEll08MainReductionActual input theorem38 (paper-input; §3 lines 738-1199)"),
    ("§4 Cor 4.3/4.4", "GenEll08MainReductionActual inputs cor43 cor44 (paper-input; §4 lines 1200-1425)"),
    ("IUT Thm 1.10 + Cor 2.2", "CaseII K ht logDiff logCond eps from the Step XI log-volume wall (paper/route consumer)") ]

end LeanFormal.IUT.XiFPaper.GenEll09IUTIVSection2ConsumerActual

end
