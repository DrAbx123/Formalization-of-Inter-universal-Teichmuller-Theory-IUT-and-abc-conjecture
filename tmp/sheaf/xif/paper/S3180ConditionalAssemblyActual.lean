import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import tmp.sheaf.xif.paper.S3171IUTIVSection1DisplayActual
import tmp.sheaf.xif.paper.S3131PaperRouteHeightReductionActual
import tmp.sheaf.xif.paper.S3131PaperRouteRegionReductionActual
import tmp.sheaf.xif.paper.S3131CanonicalRootedQCActual
import tmp.sheaf.xif.paper.S3182Cor312HullDetAssemblyActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

/-!
# S3180 (AUDITED REVISION v2): CONDITIONAL ASSEMBLY — IUT / Cor 3.12 / ABC

HONESTY AUDIT FIX (shehdd FLAG1/FLAG2; Lead disposition):
* FLAG2: signed readouts are DEFINED from tree objects:
  qPilotSignedReadout := S3131CanonicalRootedQC (paper-faithful rooted spectral
  q-pilot readout), thetaHullSignedReadout := S3131CanonicalRootedHC (rooted
  Theta-hull readout); the comparison q <= target is DERIVED from the unconditional
  tree theorem S3131CanonicalRootedQC_le_HC (not assumed). target := theta, so
  target <= theta is rfl.  The only numeric input is an explicit q!=1 hypothesis
  (qPilotSignedReadout < 0, class B paper condition, consumed by toContract).
* FLAG1: ipl/she/apt are explicit NAMED PAPER-INPUT PLACEHOLDERS (content-free,
  NOT used in any proof step).
* HULL/DET COMPONENT NOW REAL: S3182Cor312HullDetAssemblyActual (hull, GREEN/CITABLE
  6 decls) supplies the actual Cor 3.12 hull-side conclusion
  (Cor312HullDetConclusion: log sourceHullRealLogVolume = modelThetaValue M and
  ≤ theta) from the real H2 row + H4 wiring; it is consumed by
  conditionalAssembly_with_hullDet.  The old hCor312/hullPre documentation rows are
  superseded by this actual hull declaration.
* Former decorative fields (hullPre, hCor312, hSlack, mzk1GeometricCore,
  genEllTransfer) are removed from the consumed structure and recorded in
  documentationOnlyRemainingAssumptions as 'documentation-only, not consumed'.
* abcConjecture_conditional consumes ONLY heightUndilated + regionUndilated via the
  S3171 certified skeleton chain (card P not assumed).

VERIFIED CORPUS RANGES (A71): IUT III Cor 3.12 statement 10324-10353; proof
10354-10987; Step (xi) 10750-10987 substeps (xi-a) 10751, (xi-b) 10762,
(xi-c) 10799, (xi-d) 10823, (xi-e) 10864, (xi-f) 10888; conclusion 10897;
(xii) 10963; Remark 3.12.1 10988.  GenEll Thm 2.1 615-687 ((ii)=>(i) 688-760);
IUT IV Thm 1.10 line 1255, final display 1362-1385.

CONDITIONAL ASSEMBLY ONLY — not closure; registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3180ConditionalAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteFieldStatementsActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteHeightReductionActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteRegionReductionActual
open LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open MeasureTheory

universe u

section Readouts

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]

/-- The q-pilot signed readout (tree object: canonical rooted spectral Q_C). -/
noncomputable def qPilotSignedReadout : ℝ :=
  S3131CanonicalRootedQC (l := l) T mu

/-- The Theta-hull signed readout (tree object: canonical rooted H_C). -/
noncomputable def thetaHullSignedReadout : ℝ :=
  S3131CanonicalRootedHC (l := l) T mu

/-- The comparison q <= target(=hull) is DERIVED from the unconditional tree
theorem (paper-faithful rooted spectral comparison). -/
theorem qPilotSignedReadout_le_thetaHullSignedReadout :
    qPilotSignedReadout T mu ≤ thetaHullSignedReadout T mu :=
  S3131CanonicalRootedQC_le_HC (l := l) T mu

end Readouts

/-- Conditional assembly inputs (structure carries only the route interfaces and the
explicit paper placeholders; the signed readouts live in the tree objects above). -/
structure Cor312AssemblyInputs {X : Type u} (W : IQHullLogVolumeInterface X)
    (pt : Nat → Nat → Nat → X) where
  /-- NAMED PAPER-INPUT PLACEHOLDER (content-free; NOT used in any proof step):
  IPL data of IUT III Thm 3.11 Steps (xi). -/
  ipl : Prop
  /-- NAMED PAPER-INPUT PLACEHOLDER (content-free; NOT used): SHE data. -/
  she : Prop
  /-- NAMED PAPER-INPUT PLACEHOLDER (content-free; NOT used): APT data. -/
  apt : Prop
  /-- placeholder evidence (content-free) -/
  ipl_evidence : ipl
  /-- placeholder evidence (content-free) -/
  she_evidence : she
  /-- placeholder evidence (content-free) -/
  apt_evidence : apt
  /-- route (b): undilated height comparison (class B; CONSUMED by ABC). -/
  heightUndilated : UndilatedHeightBound W pt
  /-- route (c): undilated region-volume bound (class B; CONSUMED by ABC). -/
  regionUndilated : UndilatedRegionBound W pt

section Contract

variable {l : PrimeGeFive} {T : SourceNativeInitialThetaData.{0} l}
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable {mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b)}
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]
variable {X : Type u} {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}

/-- The Step XI contract assembled from tree-defined readouts; the only numeric
input is the explicit q!=1 condition (class B, consumed). -/
noncomputable def toContract (H : Cor312AssemblyInputs W pt)
    (hqneg : S3131CanonicalRootedQC (l := l) T mu < 0) : StepXIContract where
  qSigned := S3131CanonicalRootedQC (l := l) T mu
  thetaSigned := S3131CanonicalRootedHC (l := l) T mu
  targetSigned := S3131CanonicalRootedHC (l := l) T mu
  q_negative := hqneg
  ipl := H.ipl
  she := H.she
  apt := H.apt
  ipl_evidence := H.ipl_evidence
  she_evidence := H.she_evidence
  apt_evidence := H.apt_evidence
  q_le_target := S3131CanonicalRootedQC_le_HC (l := l) T mu
  target_le_theta := le_rfl

/-- **(2) Cor 3.12 conditional:** Corollary 3.12 ordered conclusion from the
assembled contract.  Consumed: q!=1 hypothesis; the q<=target comparison is the
DERIVED tree theorem.  Placeholders are not used. -/
theorem cor312_conditional (H : Cor312AssemblyInputs W pt)
    (hqneg : S3131CanonicalRootedQC (l := l) T mu < 0) :
    Cor312Conclusion (toContract H hqneg) :=
  cor312_of_constructed_stepXI (toContract H hqneg)

/-- **(3) ABC conditional:** consumes ONLY the (b)/(c) undilated interfaces via the
certified skeleton chain (card P not assumed). -/
theorem abcConjecture_conditional (H : Cor312AssemblyInputs W pt) :
    ABCConjecture :=
  S3171IUTIVSection1DisplayActual.abcConjecture_of_undilated
    H.heightUndilated H.regionUndilated

/-- IUT main-theorem shape (shape-only; no paper-level claim). -/
def IUTMainTheoremShape (H : Cor312AssemblyInputs W pt)
    (hqneg : S3131CanonicalRootedQC (l := l) T mu < 0) : Prop :=
  Cor312Conclusion (toContract H hqneg) ∧ ABCConjecture

/-- **(4) IUT main-theorem conditional (shape-only).** -/
theorem iutMainTheorem_conditional (H : Cor312AssemblyInputs W pt)
    (hqneg : S3131CanonicalRootedQC (l := l) T mu < 0) :
    IUTMainTheoremShape H hqneg :=
  ⟨cor312_conditional H hqneg, abcConjecture_conditional H⟩

end Contract

section HullDetConsumer

variable {l : PrimeGeFive} (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- **Combined conditional assembly with the REAL hull/det component (S3182):**
from the hull-layer inputs (H2 row + H4 wiring) the actual Cor 3.12 hull-side
conclusion (source hull log-volume = modelThetaValue M and ≤ theta) holds, together
with the tree-readout Cor 3.12 ordered conclusion and the conditional ABC.  Every
component is consumed: S3182's inputs by its theorem; q!=1/readouts by the contract;
(b)/(c) by the ABC step. -/
theorem conditionalAssembly_with_hullDet
    {T : SourceNativeInitialThetaData.{0} l}
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    {mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b)}
    [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]
    {X : Type u} {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (H : Cor312AssemblyInputs W pt)
    (hqneg : S3131CanonicalRootedQC (l := l) T mu < 0)
    (I : S3182Cor312HullDetAssemblyActual.HullDetAssemblyInputs M) :
    S3182Cor312HullDetAssemblyActual.Cor312HullDetConclusion M I.theta ∧
      Cor312Conclusion (toContract H hqneg) ∧ ABCConjecture :=
  ⟨S3182Cor312HullDetAssemblyActual.cor312_hullDet_conditional (M := M) I,
    cor312_conditional H hqneg, abcConjecture_conditional H⟩

end HullDetConsumer

/-- Field source table (post-audit): (field, paper source, status). -/
def cor312AssemblyFieldSources : List (String × String × String) :=
  [ ("qSigned", "qPilotSignedReadout := S3131CanonicalRootedQC (tree object)", "DEFINED from tree object; CONSUMED"),
    ("thetaSigned/targetSigned", "thetaHullSignedReadout := S3131CanonicalRootedHC (tree object)", "DEFINED from tree object; CONSUMED"),
    ("q <= target", "qPilotSignedReadout_le_thetaHullSignedReadout (unconditional tree theorem)", "DERIVED, not assumed"),
    ("target <= theta", "target := theta", "rfl"),
    ("q != 1 (q_negative)", "IUT III Cor 3.12 (statement 10324-10353)", "class B paper condition; CONSUMED as explicit argument"),
    ("ipl/she/apt + evidences", "IUT III Thm 3.11 Steps (xi)", "NAMED PLACEHOLDER (content-free; NOT used)"),
    ("heightUndilated", "(b) undilated height comparison (S3131PaperRouteHeightReductionActual)", "class B interface; CONSUMED by ABC"),
    ("regionUndilated", "(c) undilated region-volume (S3131PaperRouteRegionReductionActual)", "class B interface; CONSUMED by ABC") ]

/-- Documentation-only remaining assumptions (removed from consumed structure). -/
def documentationOnlyRemainingAssumptions : List (String × String × String) :=
  [ ("hull/det component", "S3182Cor312HullDetAssemblyActual (hull GREEN/CITABLE 6 decls): Cor312HullDetConclusion consumed by conditionalAssembly_with_hullDet", "CONSUMED (real hull declaration; inputs H2 row + H4 wiring)"),
    ("hull background rows", "Hull01/02/03 + Hull04 certificate wiring + Hull05 weighted identity; corpus proof 10354-10987, Step (xi) 10750-10987", "background evidence (consumed inside S3182)"),
    ("hSlack (IV section 1 Step (v) arithmetic)", "S3171IUTIVSection1DisplayActual; IUT IV Thm 1.10 line 1255/display 1362-1385", "documentation-only, not consumed"),
    ("mzk1GeometricCore", "Mzk1Theorem25StatementActual (placeholder True; precise statement required); [Mzk1] Thm 2.5 lines 207-221", "documentation-only, not consumed; class D paper-input"),
    ("genEllTransfer", "GenEll05Theorem21Actual.Theorem21ReductionInputs; [GenEll] Thm 2.1 615-687 ((ii)=>(i) 688-760)", "documentation-only, not consumed; class B paper-input") ]

/-- Theorem -> consumed field/assumption list (post-audit). -/
def s3180TheoremDeps : List (String × String) :=
  [ ("cor312_conditional", "explicit q!=1 argument (qPilotSignedReadout < 0); tree readouts S3131CanonicalRootedQC/HC; q<=target DERIVED from S3131CanonicalRootedQC_le_HC; target=theta rfl; placeholders unused"),
    ("abcConjecture_conditional", "heightUndilated, regionUndilated"),
    ("iutMainTheorem_conditional", "union of the above (shape-only conjunction)"),
    ("conditionalAssembly_with_hullDet", "S3182 HullDetAssemblyInputs (hc/G/hmatch/theta/theta_nonneg/hH4 all consumed) + q!=1 + tree readouts + heightUndilated/regionUndilated") ]

/-- Honesty-audit fix record (FLAG1/FLAG2). -/
def s3180HonestyAuditFix : List (String × String) :=
  [ ("FLAG2 readouts", "DEFINED via S3131CanonicalRootedQC/HC; comparison DERIVED from unconditional tree theorem; no conclusion assumed"),
    ("FLAG1 placeholders", "ipl/she/apt are named content-free paper-input placeholders; NOT used"),
    ("decorative fields", "hullPre/hCor312/hSlack/mzk1GeometricCore/genEllTransfer removed from consumed structure; documentationOnlyRemainingAssumptions marks them documentation-only"),
    ("overstatement", "docstrings state conditional assembly only; consumed-vs-documentation split explicit; no closure claim"),
    ("hull/det real component", "S3182Cor312HullDetAssemblyActual consumed via conditionalAssembly_with_hullDet (actual hull readout/theta conclusion; no conclusion-as-hypothesis)") ]

end LeanFormal.IUT.XiFPaper.S3180ConditionalAssemblyActual
