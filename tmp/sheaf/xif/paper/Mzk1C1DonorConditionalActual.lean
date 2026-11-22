/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.n8.closure.NativeC1PaperSource
import tmp.sheaf.n8.closure.C2Actual
import tmp.sheaf.xif.paper.Mzk1QPilotLineLActual
import Mathlib.Tactic

/-! # A963 hull: C1 donor conditional construction (pure plumbing)

Status: CONDITIONAL (not an unconditional existence theorem).
Hypotheses are exactly the five fields of `NativeC1PaperSource`: X, S, e,
R (NativeImageRealizationSourceFields X (assemblyInput X S e)),
F (NativeFiberSourceFields X (assemblyInput X S e) (nativePlaceIndexEquiv X)).
From them we construct the packet, its SourceInputBinding (C1), C2 via
`C2Actual.sourceLogKummerDataActual`, and the L-side `QPilotLineActualL`;
C3 uses the L carrier; `QPilotLineActualL` is specialized to `FinitePrimePlace 2 7`, while the packet input is `NativePlaces X.S`, so C3L needs a carrier identification (GAP).  R/F remain unconstructed (A948). Full QPilotLineActualL is fixed at FinitePrimePlace 2 7 by S1391; a generic C1+C2 core is provided here, C3L needs a generic SourcePilotRegionDataL (GAP). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1C1DonorConditionalActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeClosure
open LeanFormal.IUT.N8Closure.C1Actual
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeBindingRFActual
open LeanFormal.IUT.N8Closure.C2Actual
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.NativeC1PaperSource
open LeanFormal.IUT.N8Closure.NativeC1PaperSource.NativeC1PaperSource
open LeanFormal.IUT.N8Closure.PaperQPilotLineLActual
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization

variable {l : PrimeGeFive}

/-- The exact conditional hypotheses for a C1 donor (the five packet fields). -/
structure NativeC1DonorHypotheses where
  X : N8NativeInput l
  S : NativeSourceAssembly X.S
  e : X.family.index ≃ SourceTheorem311Index
  R : NativeImageRealizationSourceFields X (assemblyInput X S e)
  F : NativeFiberSourceFields X (assemblyInput X S e) (nativePlaceIndexEquiv X)

/-- Packet from the hypotheses (pure term construction). -/
noncomputable def packetOfHypotheses (H : NativeC1DonorHypotheses (l := l)) :
    NativeC1PaperSource l :=
  { X := H.X, S := H.S, e := H.e, R := H.R, F := H.F }

theorem nonempty_packet_ofHypotheses (H : NativeC1DonorHypotheses (l := l)) :
    Nonempty (NativeC1PaperSource l) :=
  ⟨packetOfHypotheses H⟩

/-- C1 source input binding from the hypotheses. -/
theorem sourceInputBinding_nonempty_ofHypotheses
    (H : NativeC1DonorHypotheses (l := l)) :
    Nonempty (SourceInputBinding (packetOfHypotheses H).input) :=
  sourceInputBinding_nonempty_of_packet (packetOfHypotheses H)

/-- C1 data from the same packet. -/
theorem nativeOldC1Bridge_nonempty_ofHypotheses
    (H : NativeC1DonorHypotheses (l := l)) :
    Nonempty (NativeOldC1Bridge (packetOfHypotheses H).X) :=
  nativeOldC1Bridge_nonempty_of_packet (packetOfHypotheses H)

/-- C2 log-Kummer data, constructed from C1 by C2Actual. -/
theorem sourceLogKummerData_nonempty_ofHypotheses
    (H : NativeC1DonorHypotheses (l := l)) :
    Nonempty (SourceLogKummerData (packetOfHypotheses H).input
      (packetOfHypotheses H).sourceInputBinding) :=
  sourceLogKummerData_nonempty_actual (packetOfHypotheses H).input
    (packetOfHypotheses H).sourceInputBinding


/-- Generic C1+C2 core of a q-pilot line (C3L is carrier-specific). -/
structure QPilotLineGenericCore {V : Type*} (I : OriginalInput l V) where
  C1 : SourceInputBinding I
  C2 : SourceLogKummerData I C1

theorem qPilotLineGenericCore_nonempty_ofHypotheses
    (H : NativeC1DonorHypotheses (l := l)) :
    Nonempty (QPilotLineGenericCore (packetOfHypotheses H).input) :=
  ⟨{ C1 := (packetOfHypotheses H).sourceInputBinding,
     C2 := Classical.choice (sourceLogKummerData_nonempty_ofHypotheses H) }⟩

def rows : List (String × String × String) :=
  [ ("NativeC1DonorHypotheses", "X,S,e,R,F", "DEF (conditional hypotheses)"),
    ("packet", "five fields -> NativeC1PaperSource", "PROVED (term)"),
    ("C1", "SourceInputBinding nonempty", "PROVED (from packet)"),
    ("C2", "SourceLogKummerData nonempty", "PROVED (C2Actual)"),
    ("C3L", "QPilotLineActualL fixed V=FinitePrimePlace 2 7; S1391 L data fixed too", "GAP (carrier mismatch)"),
    ("generic core", "QPilotLineGenericCore C1+C2 for any V", "PROVED (from hypotheses)"),
    ("R/F", "not constructed; A948 gap", "GAP") ]

theorem rows_length : rows.length = 7 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1C1DonorConditionalActual.nonempty_packet_ofHypotheses
#print axioms LeanFormal.IUT.XiFPaper.Mzk1C1DonorConditionalActual.sourceInputBinding_nonempty_ofHypotheses
#print axioms LeanFormal.IUT.XiFPaper.Mzk1C1DonorConditionalActual.sourceLogKummerData_nonempty_ofHypotheses
#print axioms LeanFormal.IUT.XiFPaper.Mzk1C1DonorConditionalActual.qPilotLineGenericCore_nonempty_ofHypotheses

end LeanFormal.IUT.XiFPaper.Mzk1C1DonorConditionalActual

end