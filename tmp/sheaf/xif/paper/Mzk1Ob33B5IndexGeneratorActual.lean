/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Ob33B5IndexActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1GeneratorValuationRelationActual
import tmp.sheaf.xif.paper.Mzk1B5CountLocalValuationBridgeActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5CountUnconditionalAttemptActual
import Mathlib.Tactic

/-! # P7 #3 OB33-SRC: actual generator for the B5 index (LFI official) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Ob33B5IndexGeneratorActual

open LeanFormal.IUT
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5IndexActual
open LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedFractionalIdealActual
open LeanFormal.IUT.XiFPaper.Mzk1B5CountLocalValuationBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1GeneratorValuationRelationActual

variable {k : Type} [Field k] [NumberField k]

/-- Actual LocalGeneratorData from the DVR IsPrincipal instance (LFI official). -/
noncomputable def generatorDataActual (I : LineBundle (k := k))
    (v : NumberField.FinitePlace k) : LocalGeneratorData (k := k) I v := by
  classical
  haveI : (localizedLine (k := k) I v).IsPrincipal :=
    localizedLine_isPrincipal_actual (k := k) I v
  refine ⟨Submodule.IsPrincipal.generator (localizedLine (k := k) I v), ?_⟩
  change localizedLine (k := k) I v =
    Submodule.span (LocalRing (k := k) v)
      {Submodule.IsPrincipal.generator (localizedLine (k := k) I v)}
  exact (Submodule.IsPrincipal.span_singleton_generator _).symm

/-- The exact missing general SNF object is now constructed (rank one). -/
theorem missingGeneralPlaceSNF_proved : MissingGeneralPlaceSNF (k := k) :=
  fun I v => ⟨placeSNFDataOfGenerator (k := k) I v (generatorDataActual (k := k) I v)⟩

/-- Per-place SNF index is the generator valuation. -/
theorem placeSNFIndex_eq_localValuation (I : LineBundle (k := k))
    (v : NumberField.FinitePlace k) :
    (placeSNFDataOfGenerator (k := k) I v (generatorDataActual (k := k) I v)).index =
      PaperOModuleActual.localValuation (k := k) v
        (generatorDataActual (k := k) I v).generator := rfl

/-- CountValuationBridge from the span-generator valuation lemma. -/
theorem countValuationBridge_of_spanGeneratorValuation
    (h : Mzk1Ob33B5CountUnconditionalAttemptActual.SpanGeneratorValuationLemma k)
    {I : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (d : LocalGeneratorData (k := k) I v) :
    Mzk1B5CountLocalValuationBridgeActual.CountValuationBridge d :=
  (countValuationBridge_iff_spanGeneratorValuation d).mpr (h v d)

section QPilot

open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperQPilotLineBundleSourceActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The per-place generator bridge for the actual q-pilot source is constructed. -/
theorem qPilotLocalGeneratorBridge_proved
    (v : NumberField.FinitePlace T.arithmetic.K) :
    QPilotLocalGeneratorBridge T v :=
  ⟨generatorDataActual (k := T.arithmetic.K) (qPilotSourceLine T) v⟩

end QPilot

def b5IndexGeneratorRows : List (String × String × String) :=
  [ ("generatorDataActual", "LocalGeneratorData from LFI IsPrincipal", "CONSTRUCTED (no assumptions)"),
    ("missingGeneralPlaceSNF_proved", "MissingGeneralPlaceSNF closed", "PROVED"),
    ("placeSNFIndex_eq_localValuation", "SNF index = generator valuation", "PROVED"),
    ("countValuationBridge_of_spanGeneratorValuation", "span lemma => CountValuationBridge", "PROVED (conditional)") ]

theorem b5IndexGeneratorRows_length : b5IndexGeneratorRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Ob33B5IndexGeneratorActual

end