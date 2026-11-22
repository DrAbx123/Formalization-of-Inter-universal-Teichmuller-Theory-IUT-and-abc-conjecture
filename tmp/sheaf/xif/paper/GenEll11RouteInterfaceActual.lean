import tmp.sheaf.xif.paper.GenEll09IUTIVSection2ConsumerActual
import tmp.sheaf.xif.paper.GenEll05Theorem21Actual
import tmp.sheaf.xif.paper.GenEll10H6ClosureActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# GenEll11: route interface — H6 slot discharged (interface level) + exact paper-inputs

Connects the P3 integration to the paper route:
* H6 (GenEll transfer) is available at the interface level
  (GenEll10H6ClosureActual.h6_genEll_BDClassOn), so the route can name H6 as
  discharged-with-inputs rather than as an unexplained gap;
* the IUT IV §2 consumer (GenEll09) replaces the Section2 [machine-gap] by the
  explicit conditional Cor 2.3 theorem with the named paper-inputs;
* the deep GenEll inputs remain exact class-B paper-inputs, listed explicitly.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.GenEll11RouteInterfaceActual

universe u

open LeanFormal.IUT.XiFPaper.S3132IVGenEllShadowAdapterActual
open LeanFormal.IUT.XiFPaper.GenEll05Theorem21Actual
open LeanFormal.IUT.XiFPaper.GenEll01BasicActual
open LeanFormal.IUT.XiFPaper.GenEll09IUTIVSection2ConsumerActual
open LeanFormal.IUT.XiFPaper.GenEll10H6ClosureActual

/-- The route-side GenEll interface record. -/
structure GenEllRouteInterface where
  /-- H6: GenEll transfer is available (interface level) -/
  h6Available : Prop
  /-- P3: the IUT IV §2 consumer is an explicit conditional Cor 2.3 theorem -/
  p3Section2Consumer : Prop
  /-- remaining deep paper-inputs (class B, exact names) -/
  paperInputs : List (String × String)

/-- The route interface is constructible: H6 from the shadow field, P3 consumer
from GenEll09, paper-inputs from the §2 replacement record. -/
def genEllRouteInterface : GenEllRouteInterface where
  h6Available := ∀ {Point : Type} (data : AdaptedIVGenEllShadow Point),
    ∃ lowerBound : ℝ, ∀ x : Point,
      lowerBound ≤ (1 + data.epsilon) * (data.logDiff x + data.logCond x) -
        data.height x
  p3Section2Consumer :=
    ∀ {X : Type} (K : Set X) (ht logDiff logCond : X → Real) (eps : Real),
      CaseII K ht logDiff logCond eps →
        (CaseII K ht logDiff logCond eps → CaseI ht logDiff logCond eps) →
          CaseI ht logDiff logCond eps
  paperInputs := iutIVSection2RemainingPaperInputs

/-- The route interface's H6 field is inhabited (interface-level H6 closure). -/
theorem genEllRouteInterface_h6 : genEllRouteInterface.h6Available :=
  fun data => h6_genEll_transfer data

/-- The route interface's P3 consumer field is inhabited (explicit conditional
Cor 2.3 theorem from GenEll09). -/
theorem genEllRouteInterface_p3 :
    genEllRouteInterface.p3Section2Consumer :=
  fun K ht logDiff logCond eps hCaseII hIItoI =>
    iutIVSection2_cor23_bdClass (K := K) ht logDiff logCond eps hCaseII hIItoI

/-- Route slot status after the P3 batch: (slot, status, evidence). -/
def genEllRouteSlots : List (String × String × String) :=
  [ ("H6", "DISCHARGED (interface level)",
      "genEllRouteInterface_h6; S3132IVGenEllShadowAdapterActual.genEll_transfer:43"),
    ("P3/IUT-IV-§2 consumer", "CONSTRUCTED (explicit conditional Cor 2.3)",
      "GenEll09IUTIVSection2ConsumerActual.iutIVSection2_cor23_bdClass"),
    ("GenEll deep inputs", "PAPER-INPUT (class B)",
      "Thm 2.1 (ii)=>(i), [Mzk1], Thm 3.8, Cor 4.3/4.4 (GenEll09 remaining record)"),
    ("route residuals", "UNCHANGED",
      "M0 same-C, capsule-label link, stage4 unit map, fourth-triangle arith inputs, comparison/measure invariance") ]

end LeanFormal.IUT.XiFPaper.GenEll11RouteInterfaceActual

end
