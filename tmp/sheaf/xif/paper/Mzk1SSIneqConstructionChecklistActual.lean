import Mathlib.Data.Real.Basic

/-!
# stepxi SSIneq construction checklist (A744)

Executable checklist of the exact constructive data needed to prove
`Iut.Wall.SSIneq D` (lana `Iut/Wall/MultiContainer.lean:88`):

  `(sFactor (nC D) - 1) * D.qPilot.absLogQ ≤ logVol D (hullOf D (vcI D))`.

Constructors (source lines):
* `Region D := ∀ i : Fin (VC D).proc.length, (VC D).AdmissibleRegion i`
  (`Iut/Wall/Rss.lean:314`);
* `vcI D : Region D := vcIAt D` (`Iut/Wall/Ind3.lean:123`, with
  `vcIComp`/`vcIAt` constructors at 58/80);
* `hullOf D U : Region D := (LocalTheory.hull ...).hullFamily U`
  (`Iut/Wall/Rss.lean:328`);
* `Ind3 D := {S : Region D // IsAdelic D S ∧ ∀ i, S i ≤ hullOf D (vcI D) i}`
  (`Iut/Wall/Ind3.lean:213`), with `Ind3.base`/`Ind3.top` at 216/220;
* `logVol D U : ℝ := (LocalTheory.vol ...).processionVol U`
  (`Iut/Wall/Rss.lean:324`).

`xi_iff_ss` (`Iut/LogLink/Thm311.lean:219`) reduces `XiPrinciple` to this target.
The checklist below records the data as explicit fields; it does not prove SSIneq. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1SSIneqConstructionChecklistActual

/-- Constructive data required for `SSIneq D`. -/
structure SSIneqData where
  /-- capsule carrier `Fin (VC D).proc.length`. -/
  capsule : Type
  /-- region type `∀ i, (VC D).AdmissibleRegion i`. -/
  Region : Type
  /-- log-shell container `vcI D`. -/
  vcI : Region
  /-- hull constructor `hullOf D`. -/
  hullOf : Region → Region
  /-- procession log-volume `logVol D`. -/
  logVol : Region → Real
  /-- `sFactor (nC D)`. -/
  sFactor : Real
  /-- `D.qPilot.absLogQ`. -/
  absLogQ : Real
  /-- `Ind3 D` subtype, with its two constructors. -/
  Ind3 : Type
  Ind3_mk : Region → Ind3
  Ind3_val : Ind3 → Region
  /-- `Ind3.base = ⟨vcI, isAdelic_vcI, vcI_le_hullOf⟩`. -/
  Ind3_base : Ind3
  /-- `Ind3.top = ⟨hullOf vcI, isAdelic_hullOf_vcI, ...⟩`. -/
  Ind3_top : Ind3

/-- The SSIneq target shape (not asserted). -/
def SSIneqTarget (D : SSIneqData) : Prop :=
  (D.sFactor - 1) * D.absLogQ ≤ D.logVol (D.hullOf D.vcI)

/-- If the data are instantiated by the lana constructors, this is exactly the
  `SSIneq` target (definitional shape). -/
theorem SSIneqTarget_eq (D : SSIneqData) :
    SSIneqTarget D ↔
      (D.sFactor - 1) * D.absLogQ ≤ D.logVol (D.hullOf D.vcI) :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.Mzk1SSIneqConstructionChecklistActual

