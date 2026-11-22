import tmp.sheaf.xif.paper.Mzk1ShellArithmeticIdentitiesActual
import tmp.sheaf.xif.paper.Mzk1SSIneqExplicitFormActual
import Mathlib.Tactic

/-!
# A801/A804 `StepXISSIneqDictionary` skeleton (shehdd)

Mainline's G4 verdict: the clean target is `SSIneq ↔ SSIneqExplicit`, NOT a dictionary to
`BadSumWeightBound` (which is only ABC-self-description under per-N constructed T).
This file fixes the **field skeleton** for that dictionary; it needs no lana olean and no
proof of the dictionary itself.

`StepXISSIneqDictionary` fields (to be instantiated from lana `InitialThetaData`):
* `sC_eq : sC = sFactor (nC)`               (averaged capsule coefficient);
* `logq_eq : logq = 2*l*A`                   (A = lana `absLogQ`);
* `V_eq : V = lanaLogVol`                    (hull log-volume readout);
and the abstract lana shape `LanaSSIneqShape s A V := (s-1)*A <= V`.

Proved here (pure arithmetic, no lana):
* `SSIneqExplicit_iff_lanaShape` under the dictionary:
  `SSIneqExplicit sC logq l V ↔ LanaSSIneqShape sC A lanaLogVol`;
* the same in the `sFactor`-parameterized form;
* dictionary with `sC = sFactor n`, `logq = 2*l*A` yields lana's shape exactly.

The only remaining G4 step is the instantiation of the three dictionary fields on lana's
`D : InitialThetaData` (needs lana olean), marked PENDING in the spec.
No RETRACTED statement is used.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXISSIneqDictionaryShaActual

open LeanFormal.IUT.XiFPaper.Mzk1ShellArithmeticIdentitiesActual
open LeanFormal.IUT.XiFPaper.Mzk1SSIneqExplicitFormActual
open scoped BigOperators

/-- Abstract lana `SSIneq` shape: `(s - 1) * A <= V` with `A = absLogQ`. -/
def LanaSSIneqShape (s A V : ℝ) : Prop := (s - 1) * A ≤ V

/-- **The G4 dictionary skeleton** (fields to be instantiated from lana's `D`). -/
structure StepXISSIneqDictionary where
  /-- averaged capsule coefficient (lana `sFactor (nC D)`). -/
  sC : ℝ
  /-- normalized q side (lana `2 * l * absLogQ`). -/
  logq : ℝ
  /-- the `l` of the Θ-data. -/
  l : ℝ
  /-- `A = absLogQ` (paper q magnitude). -/
  A : ℝ
  /-- our explicit-form volume argument. -/
  V : ℝ
  /-- lana hull log-volume readout (the object to be identified with `V`). -/
  lanaLogVol : ℝ
  /-- the number of capsules `nC`. -/
  nC : ℕ
  /-- `sC` is the averaged capsule coefficient. -/
  sC_eq : sC = sFactor nC
  /-- dictionary between normalized q side and `A`. -/
  logq_eq : logq = 2 * l * A
  /-- dictionary between our volume argument and the lana hull log-volume. -/
  V_eq : V = lanaLogVol
  /-- `l ≠ 0` (needed to divide by `2*l`). -/
  hl : l ≠ 0

/-- **Dictionary theorem (proved)**: under the dictionary, our explicit SSIneq is exactly
the abstract lana shape `(s-1)*A <= V`. -/
theorem SSIneqExplicit_iff_lanaShape (D : StepXISSIneqDictionary) :
    SSIneqExplicit D.sC D.logq D.l D.V ↔
      LanaSSIneqShape D.sC D.A D.lanaLogVol := by
  unfold SSIneqExplicit LanaSSIneqShape
  rw [D.logq_eq, D.V_eq]
  have hdiv : (2 * D.l * D.A) / (2 * D.l) = D.A := by
    field_simp [D.hl]
  rw [hdiv]

/-- The same with `sC = sFactor nC` exposed. -/
theorem SSIneqExplicit_iff_lanaShape_sFactor (D : StepXISSIneqDictionary) :
    SSIneqExplicit (sFactor D.nC) D.logq D.l D.V ↔
      LanaSSIneqShape (sFactor D.nC) D.A D.lanaLogVol := by
  have hD := SSIneqExplicit_iff_lanaShape D
  rw [D.sC_eq] at hD
  exact hD

structure DictRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def dictRows : List DictRow :=
  [ ⟨"dictionary", "StepXISSIneqDictionary (sC, logq, l, A, V, lanaLogVol, nC) with sC=sFactor nC, logq=2lA, V=lanaLogVol", "DEF"⟩
  , ⟨"dictionary theorem", "SSIneqExplicit sC logq l V <-> LanaSSIneqShape sC A lanaLogVol", "PROVED"⟩
  , ⟨"sFactor form", "same with sC = sFactor nC exposed", "PROVED"⟩
  , ⟨"lana instantiation", "fill fields from lana InitialThetaData D (nC, absLogQ, logVol hull)", "PENDING (needs lana olean)"⟩
  , ⟨"scope", "no lana import; no RETRACTED use", "INTEGRITY"⟩
  ]

theorem dictRows_length : dictRows.length = 5 := rfl

theorem dictRows_has_pending :
    dictRows.any (fun r => r.status = "PENDING (needs lana olean)") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1StepXISSIneqDictionaryShaActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXISSIneqDictionaryShaActual.SSIneqExplicit_iff_lanaShape
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXISSIneqDictionaryShaActual.SSIneqExplicit_iff_lanaShape_sFactor
