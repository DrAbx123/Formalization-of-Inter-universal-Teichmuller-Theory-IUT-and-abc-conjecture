/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull
import Mathlib.Tactic

/-! # A986: realified value monoid and SourceImageRealization producer

**MODEL/REALIFICATION, not a toy carrier.**  This file builds the realified
value group used by the paper's D^⊢ source image:
- `realifiedFPrimeStrip V`: an `FPrimeStrip` whose value monoid is the
  multiplicative group of positive reals `Multiplicative ℝ`, with degree the
  identity (`Multiplicative.toAdd`), trivial Pi/G action;
- `RealifiedValueMonoidAt I v`: a realification datum at an actual input:
  a monoid equivalence `I.ValueMonoidAt 0 0 v ≃* Multiplicative ℝ` commuting
  with the degree (`logDegreeAt` = `Multiplicative.toAdd`);
- `sourceImageRealizationOfRealified`: the producer of
  `I.SourceImageRealization v` from that datum, with `posRealAction` the inverse
  equivalence and `degree_of_q` proved from the commuting law.

EXACT DEVIATION / REMAINING OBLIGATION: the paper's actual local value monoid
(p-adic units / log-shell value group) is not identified with `Multiplicative ℝ`
in this file.  The identification is the explicit `RealifiedValueMonoidAt` field;
it is a realification model of the D^⊢ value group, not a proof that the actual
p-adic monoid is the real line.  `realifiedFPrimeStrip` is a model prime strip,
not an actual arithmetic source input. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1RealifiedValueMonoidActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

/-- The realified prime strip: value monoid `Multiplicative ℝ`, degree identity. -/
noncomputable def realifiedFPrimeStrip (V : Type*) : FPrimeStrip V where
  Pi := fun _ => PUnit
  groupPi := fun _ => inferInstance
  G := fun _ => PUnit
  groupG := fun _ => inferInstance
  proj := fun _ => MonoidHom.id PUnit
  proj_surjective := fun _ => Function.surjective_id
  Mon := fun _ => Multiplicative ℝ
  commMonoidMon := fun _ => inferInstance
  action := fun _ => 1
  degree := fun _ => MonoidHom.id (Multiplicative ℝ)

/-- Degree of the realified strip is `Multiplicative.toAdd`. -/
theorem realifiedFPrimeStrip_degree (V : Type*) (v : V)
    (x : (realifiedFPrimeStrip V).Mon v) :
    (realifiedFPrimeStrip V).degree v x = x := rfl

variable {l : PrimeGeFive} {V : Type*} (I : OriginalInput l V)

/-- A realification datum at the actual value monoid of `I` at `v`. -/
structure RealifiedValueMonoidAt (v : V) where
  /-- The realified value group identification. -/
  equiv : I.ValueMonoidAt 0 0 v ≃* Multiplicative ℝ
  /-- The degree is transported to the additive real coordinate. -/
  degree_eq : ∀ x : I.ValueMonoidAt 0 0 v,
    I.logDegreeAt 0 0 v x = Multiplicative.toAdd (equiv x)

namespace RealifiedValueMonoidAt

variable {I} {v : V} (R : RealifiedValueMonoidAt I v)

/-- The positive-real action induced by the realification. -/
noncomputable def posRealAction :
    Multiplicative ℝ →* I.ValueMonoidAt 0 0 v :=
  R.equiv.symm.toMonoidHom

/-- The induced action has degree exactly the real parameter. -/
theorem logDegreeAt_posRealAction (b : ℝ) :
    I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b := by
  unfold posRealAction
  have h := R.degree_eq (R.equiv.symm (Multiplicative.ofAdd b))
  rw [MulEquiv.apply_symm_apply] at h
  simpa using h

/-- **Producer**: a realification datum yields a source image realization. -/
noncomputable def sourceImageRealization : I.SourceImageRealization v where
  posRealAction := R.posRealAction
  degree_of_q := by
    exact R.logDegreeAt_posRealAction (Real.log ((I.theaterAt 0 0).thetaPacket.q))

theorem sourceImageRealization_posRealAction :
    (R.sourceImageRealization).posRealAction = R.posRealAction := rfl

end RealifiedValueMonoidAt

def rows : List (String × String × String) :=
  [ ("realifiedFPrimeStrip", "Mon=Multiplicative ℝ, degree=toAdd, action=1", "DEF (realification model)"),
    ("RealifiedValueMonoidAt", "equiv + degree commuting law", "DEF (explicit realification datum)"),
    ("posRealAction", "equiv.symm : Multiplicative ℝ →* Mon", "DEF"),
    ("logDegreeAt_posRealAction", "degree(action(ofAdd b))=b", "PROVED"),
    ("sourceImageRealization", "SourceImageRealization producer", "PROVED (from datum)"),
    ("actual p-adic identification", "not proved; h is explicit", "GAP (realification model)") ]

theorem rows_length : rows.length = 6 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1RealifiedValueMonoidActual.RealifiedValueMonoidAt.logDegreeAt_posRealAction
#print axioms LeanFormal.IUT.XiFPaper.Mzk1RealifiedValueMonoidActual.RealifiedValueMonoidAt.sourceImageRealization

end LeanFormal.IUT.XiFPaper.Mzk1RealifiedValueMonoidActual

end