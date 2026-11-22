/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Iut.Wall.MultiContainer
import Iut.Cor312.Statement

/-!
# A801 Step (xi) minimal statement (mainline)

`StepXIMinimalStatement D` is lana's Scholze–Stix inequality `Wall.SSIneq D`, unpacked;
`stepXIMinimal_iff` is a pure unfolding. The open content is inhabiting it (P6 of
`coord/STEP-XI-SPEC.md`), which is ABC-strength Szpiro-6 (A763).

PENDING-EXTERNAL: needs the lana `Iut` oleans (currently being compiled by the DAG
watchdog: Cor312/Statement → Concrete/ThetaRegion → Wall → MainTheorem).

No axiom; no sorry; ABC gate NOT passed. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIMinimalStatementActual

open Iut

/-- Step (xi) minimal statement: the Scholze–Stix inequality (lana `Wall.SSIneq`). -/
def StepXIMinimalStatement (D : InitialThetaData.{0}) : Prop :=
  Wall.SSIneq D

/-- Unfolding dictionary: `StepXIMinimalStatement` is literally the SS inequality. -/
theorem stepXIMinimal_iff (D : InitialThetaData.{0}) :
    StepXIMinimalStatement D ↔
      (sFactor (nC D) - 1) * D.qPilot.absLogQ ≤ logVol D (hullOf D (vcI D)) := Iff.rfl

/-- The iff is not the open content: this only records the definitional form. -/
theorem stepXIMinimal_iff' (D : InitialThetaData.{0}) :
    StepXIMinimalStatement D ↔ Wall.SSIneq D := Iff.rfl

end LeanFormal.IUT.XiFPaper.Mzk1StepXIMinimalStatementActual

end

/-! ### Axiom gates (top level; only once lana oleans exist) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIMinimalStatementActual.stepXIMinimal_iff
