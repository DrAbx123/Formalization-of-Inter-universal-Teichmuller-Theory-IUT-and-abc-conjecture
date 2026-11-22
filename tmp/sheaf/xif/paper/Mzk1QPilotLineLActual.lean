/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.QPilotObjectActual
import tmp.sheaf.xif.paper.S1391C3LSourcePilotActual
import Mathlib.Tactic

/-! # A935/A938: L-carrier q-pilot chain (with the impossible old CompletionRootBlock) -/

/- The old `CompletionRootBlock` (S1391:146) is obstructed (`completionRootBlock_nonempty_iff`, S1391:221).
The L-carrier `SourcePilotRegionDataL` (S1391:244) and its actual data
`actualSourcePilotRegionDataL` (S1391:329), core `sourcePilotRegionLToCore` (S1391:285),
are green.  This file defines the L-carrier line/paper-object/identification layer and
proves the parametric inhabitation; C1 (SourceInputBinding) and C2 (SourceLogKummerData)
inhabitation remain separate source obligations. -/

universe upi umon ui

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourceInputBinding

namespace LeanFormal.IUT.N8Closure.PaperQPilotLineLActual

variable {l : PrimeGeFive}

structure QPilotLineActualL
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)) where
  C1 : SourceInputBinding I
  C2 : SourceLogKummerData I C1
  C3L : SourcePilotRegionDataL (I := I)

noncomputable def QPilotLineActualL.core
    {I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)}
    (L : QPilotLineActualL I) : SourcePilotRegionCore (I := I) :=
  sourcePilotRegionLToCore I L.C3L

noncomputable def QPilotLineActualL.qScalar
    {I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)}
    (L : QPilotLineActualL I) : ℝ :=
  localSignedLog (L.core).q

theorem QPilotLineActualL.qScalar_neg
    {I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)}
    (L : QPilotLineActualL I) : L.qScalar < 0 :=
  localSignedLog_neg (L.core).q

structure PaperQPilotObjectActualL
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)) where
  line : QPilotLineActualL I
  oneZero : OneZeroPoint
  oneZero_eq : oneZero = oneZeroPoint

structure QPilotIdentificationActualL
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)) where
  object : PaperQPilotObjectActualL I
  canonicalOneZero : OneZeroPoint
  oneZero_eq : object.oneZero = canonicalOneZero

theorem qPilotIdentificationActualL_nonempty_of_object
    {I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)}
    (P : PaperQPilotObjectActualL I) :
    Nonempty (QPilotIdentificationActualL I) :=
  ⟨{ object := P, canonicalOneZero := oneZeroPoint,
     oneZero_eq := oneZeroPoint_eq P.oneZero }⟩

theorem qPilotLineActualL_nonempty_of_fields
    {I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)}
    (C1 : SourceInputBinding I) (C2 : SourceLogKummerData I C1)
    (C3L : SourcePilotRegionDataL (I := I)) :
    Nonempty (QPilotLineActualL I) :=
  ⟨⟨C1, C2, C3L⟩⟩

def qPilotLCarrierRows : List (String × String) :=
  [ ("CompletionRootBlock", "S1391:146; obstructed (completionRootBlock_nonempty_iff)") ,
    ("SourcePilotRegionDataL", "S1391:244 green; actualSourcePilotRegionDataL S1391:329") ,
    ("sourcePilotRegionLToCore", "S1391:285 green") ,
    ("QPilotLineActualL / PaperQPilotObjectActualL / QPilotIdentificationActualL", "L-carrier DEF") ,
    ("qPilotIdentificationActualL_nonempty_of_object", "PROVED (parametric)") ,
    ("qPilotLineActualL_nonempty_of_fields", "PROVED (reduces to C1/C2/C3L)") ,
    ("C1/C2 inhabitation", "OPEN (source obligations)") ]

theorem qPilotLCarrierRows_length : qPilotLCarrierRows.length = 7 := rfl

end LeanFormal.IUT.N8Closure.PaperQPilotLineLActual
