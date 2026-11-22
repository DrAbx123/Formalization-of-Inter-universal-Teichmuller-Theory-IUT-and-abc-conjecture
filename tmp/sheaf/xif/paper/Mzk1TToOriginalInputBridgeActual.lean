/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.PaperQPilotObjectSourceActual

/-! # A716: T -> OriginalInput bridge, parameterized def form (no structure universe issue) -/

/- Green constructors inventory:
* lineBundle : `OrigXiFPaperLineBundleCarrier` (OrigXiFPaperLineBundleActual.lean:175);
* logKummer : `OrigXiFPaperSourceKummerArrow` (OrigXiFPaperQPilotObjectActual.lean:356),
  `NontrivialArrowsActual.kummer` (:101);
* boundary / oneColumn: no green T-constructors found (bridges (a) remain).

Reducing the 4 constructor inputs to 2 (boundary, oneColumn) requires feeding the green
lineBundle/logKummer constructors with T's initial data; their own inputs (stripIso/layer)
are the remaining sub-bridges and are recorded as such.  This file supplies the
parameterized def form of the constructor (compiles; structure form hit a Lean universe
inference limitation on the field types). -/

noncomputable section

namespace LeanFormal.IUT
namespace Theorem311Source

open LeanFormal.IUT

universe ua uv upi umon ui uG uL uC

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}

/-- Parameterized bridge: the paper q-pilot object from the four explicit inputs. -/
noncomputable def paperQPilotObjectOfInputs
    (boundary : LeanFormal.IUT.SourceProcessionBoundary.Input (l := l) (V := V) (Label := Label) (Choice := Choice))
    (oneColumn : SourceOneColumnArithmeticHolomorphicStructure V)
    (lineBundle : LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual.PaperLineBundleCarrier (k := I.initial.arithmetic.Fmod))
    (logKummer : SourceKummerArrow G envStrip (sourceQPilotStrip boundary)) :
    PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip :=
  paperQPilotObjectSourceActual boundary oneColumn lineBundle logKummer

/-- Its q-pilot log-volume is the source signed scalar. -/
theorem paperQPilotObjectOfInputs_qPilotLogVolume
    (boundary : LeanFormal.IUT.SourceProcessionBoundary.Input (l := l) (V := V) (Label := Label) (Choice := Choice))
    (oneColumn : SourceOneColumnArithmeticHolomorphicStructure V)
    (lineBundle : LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual.PaperLineBundleCarrier (k := I.initial.arithmetic.Fmod))
    (logKummer : SourceKummerArrow G envStrip (sourceQPilotStrip boundary)) :
    (paperQPilotObjectOfInputs boundary oneColumn lineBundle logKummer).qPilotLogVolume
      = sourceQPilotSignedLog I.initial := rfl

end Theorem311Source
end LeanFormal.IUT
