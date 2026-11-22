import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC
import Mathlib

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# Mzk1Cor312ToABCConsumerActual — goal-level consumer: named paper inputs -> Cor 3.12 -> ABC

STEP 0 prior-art (reuse, no re-proof):
* LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface:
  - Cor312ToABCBridgeInterface (carrier / hullData : IQHullLogVolumeInterface carrier /
    epsilonComparison : forall eps>0, Cor312EpsilonArithmeticComparison hullData eps);
  - Cor312EpsilonArithmeticComparison with EXACTLY TWO named IUT IV gaps:
    height_le_normalizedRegionVolume (IUT IV section 2 arithmetic line-bundle comparison)
    and regionVolume_le_normalizedWeight (IUT IV section 2 main log-volume estimate,
    conditional on the Corollary 3.12 finiteness);
  - hull_logVolume_lt_top (Cor 3.12 finiteness) PROVED inside IQHullLogVolumeInterface;
  - cor312ToABCBridge_heightBound / cor312ToABCBridge_abcConjecture PROVED conditionally;
* conditional E/Hull/H6/2.4 assets CITED in the rows below (their named inputs are explicit
  in their own files): Mzk1HullEInputsActual.hullE_genEll_intermediate / hullE_cor312
  (conditional on HullEH5NamedInputs/HullEH7NamedInput), AbsTopIII05RefinedActual.
  s3171RouteSlot_display_and_abc / absTopIII05Refined_with_s3171RouteSlot, EtTh conditional
  wiring, GenEll 2.1 consumer (NOT green: record only), fold base PROVED
  (Mzk1Consumer24AdapterUnconditionalActual, finite beta / F=Q).

CONSTRUCTION (conditional, no closure claim, no circularity): a structure of NAMED PAPER
INPUTS is assembled; the Cor312ToABCBridgeInterface is built from those fields ONLY (never
from the interface's existence or from ABC); then ABCConjecture follows through the existing
proved theorem cor312ToABCBridge_abcConjecture.  The two IUT IV comparison gaps are NOT
proved here; the Cor 3.12 finiteness is inside the hull interface (proved), but the carrier
identification remains named data.  Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312ToABCConsumerActual

open LeanFormal.IUT

universe u

/-- **Named paper inputs for the Cor 3.12 -> ABC bridge.**  Every field is an explicit
paper-level input; the interface is CONSTRUCTED from these fields only. -/
structure Cor312ToABCNamedPaperInputs where
  /-- Paper carrier of the Corollary 3.12 hull interface (named data: not claimed to be
  the literal IUT III inductive system; cf. SourceHullCompactnessReduction audit note). -/
  carrier : Type u
  /-- IUT III Corollary 3.12 hull/finiteness interface.  Its finiteness theorem
  hull_logVolume_lt_top is PROVED in SourceHullCompactnessReduction. -/
  hullData : IQHullLogVolumeInterface carrier
  /-- The per-epsilon IUT IV comparison data.  Its two fields are the named paper gaps
  (height comparison and log-volume computation); nothing here asserts them. -/
  epsilonComparison : ∀ epsilon : Real, 0 < epsilon →
    Cor312EpsilonArithmeticComparison hullData epsilon

/-- Construct the Cor312ToABCBridgeInterface from the named paper inputs ONLY. -/
def cor312ToABCBridgeInterface_of_namedInputs (N : Cor312ToABCNamedPaperInputs.{u}) :
    Cor312ToABCBridgeInterface.{u} :=
  { carrier := N.carrier
    hullData := N.hullData
    epsilonComparison := N.epsilonComparison }

/-- **Goal-level conditional consumer:** named paper inputs give ABCConjecture (through the
existing proved conditional bridge theorem; no circularity, no closure claim). -/
theorem abcConjecture_of_namedInputs (N : Cor312ToABCNamedPaperInputs.{u}) :
    ABCConjecture :=
  cor312ToABCBridge_abcConjecture (cor312ToABCBridgeInterface_of_namedInputs N)

/-- Logarithmic form (through the proved equivalence). -/
theorem abcLogConjecture_of_namedInputs (N : Cor312ToABCNamedPaperInputs.{u}) :
    ABCLogConjecture :=
  cor312ToABCBridge_abcLogConjecture (cor312ToABCBridgeInterface_of_namedInputs N)

/-- The ABC-style height bound form (through the proved conditional height bound). -/
theorem heightBound_of_namedInputs (N : Cor312ToABCNamedPaperInputs.{u}) :
    ∀ epsilon : Real, 0 < epsilon → ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  cor312ToABCBridge_heightBound (cor312ToABCBridgeInterface_of_namedInputs N)

/-- **Problem E / H6 named deep assets (separate conditional layer; NOT used to construct
the bridge above — recorded so the goal-level consumer is honest about what remains).**
Each field is a named paper input of the corresponding conditional asset; none is asserted
true. -/
structure ProblemE6NamedAssets where
  /-- H5 class-B: full O(-)^{-1} normalization on the arithmetic line bundle
  (Mzk1HullEInputsActual.HullEH5NamedInputs.oInverseNormalization; tree report R9/R10). -/
  h5_oInverse_normalization : Prop
  /-- H5 class-B: hull <= image-volume inequality (HullEH5NamedInputs.hull_le_image_volume). -/
  h5_hull_le_image_volume : Prop
  /-- H7/Ob9 class-B: arbitrary log-link iterate independence of the comparison
  (HullEH7NamedInput.arbitraryIterateIndependence; Hull13 comparison consumer). -/
  h7_ob9_arbitrary_iterate : Prop
  /-- AbsTopIII05 refined route slot (AbsTopIII05RefinedActual.
  s3171RouteSlot_display_and_abc / absTopIII05Refined_with_s3171RouteSlot). -/
  absTopIII05_s3171_route_slot : Prop
  /-- EtTh conditional wiring (EtTh status/wiring layer; named class-B). -/
  etth_conditional_wiring : Prop
  /-- GenEll 2.1 consumer: NOT green (record only; pending). -/
  genEll21_consumer : Prop

/-- Inventory of named inputs with paper provenance and status. -/
def namedPaperInputRows : List (String × String × String) :=
  [ ("bridge carrier", "named data: paper-level carrier of the Cor 3.12 hull interface; not the literal IUT III inductive system", "NAMED (SourceHullCompactnessReduction audit)"),
    ("Cor 3.12 hull/finiteness interface", "IQHullLogVolumeInterface; hull_logVolume_lt_top PROVED in SourceHullCompactnessReduction", "PROVED finiteness + NAMED carrier"),
    ("IUT IV gap 1: height comparison", "Cor312EpsilonArithmeticComparison.height_le_normalizedRegionVolume (IUT IV section 2 arithmetic line-bundle comparison)", "NAMED (unproved paper link)"),
    ("IUT IV gap 2: region log-volume computation", "Cor312EpsilonArithmeticComparison.regionVolume_le_normalizedWeight (IUT IV section 2 main estimate, conditional on Cor 3.12 finiteness)", "NAMED (unproved paper link)"),
    ("E/Hull H5: O(-)^{-1} normalization", "HullEH5NamedInputs.oInverseNormalization (Mzk1HullEInputsActual; tree report R9/R10)", "NAMED class-B (separate layer; not used for bridge construction)"),
    ("E/Hull H5: hull <= image-volume", "HullEH5NamedInputs.hull_le_image_volume (Hull09H5GapsActual tree reuse)", "NAMED class-B (separate layer)"),
    ("E/Hull H7/Ob9 arbitrary iterate", "HullEH7NamedInput.arbitraryIterateIndependence (Hull13H7Ob9ComparisonConsumerActual)", "NAMED class-B (separate layer)"),
    ("s3171 route slot / AbsTopIII05 refined", "AbsTopIII05RefinedActual.s3171RouteSlot_display_and_abc / absTopIII05Refined_with_s3171RouteSlot", "CONDITIONAL ASSET (named inputs explicit)"),
    ("EtTh conditional wiring", "EtTh status/wiring layer", "CONDITIONAL / NAMED"),
    ("GenEll 2.1 consumer", "GenEll21GeometricCoreConsumerActual", "NOT GREEN (pending; record only)"),
    ("2.4 fold base (finite beta)", "Mzk1Consumer24AdapterUnconditionalActual (Problem A fold, unconditional finite beta = PROVED)", "PROVED (F=Q finite-beta; not an input to this bridge)"),
    ("conditional bridge", "cor312ToABCBridgeInterface_of_namedInputs -> cor312ToABCBridge_abcConjecture", "PROVED CONDITIONALLY (no closure claim)") ]

theorem namedPaperInputRows_length : namedPaperInputRows.length = 12 := rfl

/-- No circularity: the bridge interface is constructed from the named fields; the
ABC conclusion is the existing proved conditional theorem. -/
theorem namedInputs_construct_bridge (N : Cor312ToABCNamedPaperInputs.{u}) :
    cor312ToABCBridgeInterface_of_namedInputs N =
      ({ carrier := N.carrier, hullData := N.hullData,
         epsilonComparison := N.epsilonComparison } : Cor312ToABCBridgeInterface.{u}) := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Cor312ToABCConsumerActual

end
