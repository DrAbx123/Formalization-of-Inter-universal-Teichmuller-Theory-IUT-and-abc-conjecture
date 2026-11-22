import tmp.sheaf.xif.paper.Indet05RouteMultiradialClassActual
import tmp.sheaf.xif.paper.Indet02BPSMultiradialUpToActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Indet06: H7 / Ob9 consumer wiring for hull (Indet chain interface row)

Interface for hull's H7 (Ob9) log-link compatibility statement: the comparison
readouts of the first-triangle multiradial representation are invariant under the
permissible (Ind1)/(Ind2) indeterminacies and one-sided under (Ind3), so arbitrary
log-link iterates do not affect the Cor 3.12 comparison.  This file bundles the
Indet chain results (Indet01/02/05) into a single importable interface and provides
the concrete per-lemma consumer projections; hull's Hull08Ob9LogLinkActual may
import this file and consume the named rows (no closure claims; hull writes its own
paper-level H7/Ob9 assembly conditional on these interface rows).

A71 corpus references (per hull): Rem 3.9.4 ~7151; Step (xi) 10750-10987;
conclusion 10897.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.Indet06H7Ob9WiringActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual
open LeanFormal.IUT.XiFPaper.S3139SourceMultiradialQuotientActual
open LeanFormal.IUT.XiFPaper.Indet01FirstTriangleIndActual
open LeanFormal.IUT.XiFPaper.Indet02BPSMultiradialUpToActual
open LeanFormal.IUT.XiFPaper.Indet05RouteMultiradialClassActual

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- H7/Ob9 indeterminacy interface: permissible log-link iterate data plus the
invariance/one-sidedness laws of the comparison readout.  Every field is a PROVED
statement of the Indet chain (see h7Ob9IndetWiring). -/
structure H7Ob9IndetWiring
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  /-- the permissible log-link iterate data: the vertical (Ind3) iterates of the
  source base choice. -/
  logLinkIterate : Nat → SourceStepXIChoice I
  /-- (Ind1) invariance of the multiradial-representation (comparison) readout. -/
  ind1_invariant : ∀ (g : SourceStepXILabel) (c : SourceStepXIChoice I),
    sourceMultiradialMap I ((sourceStepXICore I).ind1 g c) = sourceMultiradialMap I c
  /-- (Ind2) invariance of the comparison readout. -/
  ind2_invariant : ∀ (g : SourceStepXILabel) (c : SourceStepXIChoice I),
    sourceMultiradialMap I ((sourceStepXICore I).ind2 g c) = sourceMultiradialMap I c
  /-- (Ind3) one-sided upper-semi monotonicity of the possible-image readout. -/
  ind3_one_sided : ∀ (n : Nat) (c : SourceStepXIChoice I) (z : ℝ),
    z ∈ sourceMultiradialPossibleImage I (sourceMultiradialMap I c) →
      ∃ w, w ∈ sourceMultiradialPossibleImage I
        (sourceMultiradialMap I ((sourceStepXICore I).ind3 n c)) ∧ z ≤ w

/-- The H7/Ob9 interface is available from the PROVED Indet05 lemmas. -/
noncomputable def h7Ob9IndetWiring
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) : H7Ob9IndetWiring I where
  logLinkIterate := fun n => (sourceStepXICore I).ind3 n (SourceStepXIBase I)
  ind1_invariant := fun g c => sourceMultiradialMap_ind1 I g c
  ind2_invariant := fun g c => sourceMultiradialMap_ind2 I g c
  ind3_one_sided := fun n c z hz =>
    sourceMultiradialPossibleImage_ind3_upper I n c z hz

/-- Consumer projection: (Ind1) leaves the comparison (multiradial) readout
invariant (PROVED; direct reuse). -/
theorem h7Ob9_comparison_ind1_invariant
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (g : SourceStepXILabel) (c : SourceStepXIChoice I) :
    sourceMultiradialMap I ((sourceStepXICore I).ind1 g c) =
      sourceMultiradialMap I c :=
  sourceMultiradialMap_ind1 I g c

/-- Consumer projection: (Ind2) leaves the comparison readout invariant (PROVED). -/
theorem h7Ob9_comparison_ind2_invariant
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (g : SourceStepXILabel) (c : SourceStepXIChoice I) :
    sourceMultiradialMap I ((sourceStepXICore I).ind2 g c) =
      sourceMultiradialMap I c :=
  sourceMultiradialMap_ind2 I g c

/-- Consumer projection: (Ind3) is one-sided on the comparison readout (PROVED). -/
theorem h7Ob9_comparison_ind3_one_sided
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Nat)
    (c : SourceStepXIChoice I) (z : ℝ)
    (hz : z ∈ sourceMultiradialPossibleImage I (sourceMultiradialMap I c)) :
    ∃ w, w ∈ sourceMultiradialPossibleImage I
        (sourceMultiradialMap I ((sourceStepXICore I).ind3 n c)) ∧ z ≤ w :=
  sourceMultiradialPossibleImage_ind3_upper I n c z hz

/-- preferred consumer file/name for hull: import this module and use
H7Ob9IndetWiring / h7Ob9IndetWiring plus the three consumer projections;
hull's file suggestion: Hull08Ob9LogLinkActual. -/
def h7Ob9ConsumerInterface : List (String × String) :=
  [ ("import", "tmp.sheaf.xif.paper.Indet06H7Ob9WiringActual"),
    ("available rows", "H7Ob9IndetWiring, h7Ob9IndetWiring, h7Ob9_comparison_ind1_invariant, h7Ob9_comparison_ind2_invariant, h7Ob9_comparison_ind3_one_sided, h7Ob9_bpsToMultiradial_ind1_ind2"),
    ("Indet chain sources", "Indet01FirstTriangleIndActual / Indet02BPSMultiradialUpToActual / Indet05RouteMultiradialClassActual"),
    ("A71 corpus refs", "Rem 3.9.4 ~7151; Step (xi) 10750-10987; conclusion 10897") ]

end LeanFormal.IUT.XiFPaper.Indet06H7Ob9WiringActual

end
