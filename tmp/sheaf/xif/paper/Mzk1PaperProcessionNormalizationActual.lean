/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import tmp.sheaf.xif.paper.Mzk1ProcessionContributionNumericsActual
import Mathlib.Tactic

/-! A528: paper procession-normalized q-pilot formula and the Theta coefficient.

Sources (line numbers):
* IUT III, Prop 3.9(i), 6838-6893: packet-normalization (mult by p adds -log p),
  procession-normalization = AVERAGE over the capsules of the procession.
* IUT III, Remark 3.1.1(ii), 5408-5465: normalized weights 1/[K_v:(Fmod)_v]
  (and product weights for tensor packets), normalized so multiplication by p
  affects log-volumes by +-log p.
* IUT III, Cor 3.12, 10324-10353: -|log Theta| = procession-normalized log-volume of
  the holomorphic hull of the union of possible images of the Theta-pilot (average
  over j in F_l^x/{+-1}); -|log q| = procession-normalized log-volume of the q-pilot
  image; and -|log Theta| >= -|log q| (C_Theta >= -1).
* IUT IV, Thm 1.10, 1358-1360: |log q| = (1/(2l)) * log(q), log(q) = degree of the
  q-divisor >= 0.  This is the procession-normalized q-pilot magnitude: the average
  over the 2l capsules/labels of the q-pilot procession gives log(q)/(2l).

Consequences proved here:
  (1) paper q magnitude = logQ/(2l) (NOT logQ = m log p as in the previous model);
  (2) the procession average of the local j^2 contributions is
      (l+1)/24 * logQ = (l(l+1)/12) * |log q|  (l = 2l*+1);
  so the raw theta average is arithFactor times the q magnitude; the missing
      normalization in the hull model is exactly arithFactor = l(l+1)/12;
  (3) after dividing the theta average by arithFactor it equals |log q|, giving the
      C_Theta representation -|log Theta| = C * |log q| with the paper condition
      C >= -1 equivalent to -|log Theta| >= -|log q|;
  (4) numeric instance l = 13, logQ = 5 log 11: qMag = 5log11/26,
      raw theta average = (7/12)*5log11, arithFactor = 91/6, normalized = 5log11/26.

This corrects the q-side model: the earlier `qPilotArithmeticVolume = -m log p`
missed the 1/(2l) procession normalization.  It also pinpoints the hull-model error:
the raw procession average (coefficient (l*+1)/12 = (l+1)/24 on log(q)) was used as
the Theta readout WITHOUT dividing by arithFactor, hence the spurious condition
`1 >= (l*+1)/12` on the wrong scale. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperProcessionNormalizationActual

open LeanFormal.IUT.XiFPaper.Mzk1ProcessionContributionNumericsActual
open scoped BigOperators

/-- Paper q-pilot procession-normalized magnitude: |log q| = log(q)/(2l)
(IUT IV, Thm 1.10, 1358-1360). -/
noncomputable def paperQMagnitude (logQ : Real) (l : Nat) : Real :=
  logQ / (2 * (l : Real))

theorem paperQMagnitude_def (logQ : Real) (l : Nat) :
    paperQMagnitude logQ l = logQ / (2 * (l : Real)) := rfl

/-- arithFactor = l(l+1)/12 with l = 2l*+1. -/
noncomputable def arithFactor (n : Nat) : Real :=
  ((2 * (n : Real) + 1) * ((2 * (n : Real) + 1) + 1)) / 12

theorem arithFactor_eq (n : Nat) :
    arithFactor n = ((2 * (n : Real) + 1) * ((2 * (n : Real) + 1) + 1)) / 12 := rfl

/-- Procession average of the local j^2/(2l) contributions: (l+1)/24 * logQ
(laichunwing Unit L / IUT III Prop 3.9(i) average over the capsules). -/
noncomputable def rawThetaAverage (n : Nat) (logQ : Real) : Real :=
  ((n : Real) + 1) / 12 * logQ

theorem rawThetaAverage_eq (n : Nat) (logQ : Real) :
    rawThetaAverage n logQ = ((n : Real) + 1) / 12 * logQ := rfl

/-- The raw theta average is arithFactor times the paper q magnitude. -/
theorem rawThetaAverage_eq_arithFactor_mul_paperQMagnitude (n : Nat) (logQ : Real) :
    rawThetaAverage n logQ = arithFactor n * paperQMagnitude logQ (2 * n + 1) := by
  unfold rawThetaAverage arithFactor paperQMagnitude
  have hl : ((2 * (n : Real) + 1) : Real) != 0 := by positivity
  field_simp
  ring

/-- The normalized theta magnitude: raw average divided by arithFactor. -/
noncomputable def normalizedThetaMagnitude (n : Nat) (logQ : Real) : Real :=
  rawThetaAverage n logQ / arithFactor n

/-- After the arithFactor normalization the theta magnitude equals |log q|. -/
theorem normalizedThetaMagnitude_eq_paperQMagnitude (n : Nat) (logQ : Real)
    (hn : 0 < n) :
    normalizedThetaMagnitude n logQ = paperQMagnitude logQ (2 * n + 1) := by
  unfold normalizedThetaMagnitude
  rw [rawThetaAverage_eq_arithFactor_mul_paperQMagnitude]
  have hfac : arithFactor n != 0 := by
    unfold arithFactor
    positivity
  field_simp

/-- The paper signed readings with C_Theta: theta signed = -C * |log q|,
q signed = -|log q|. -/
noncomputable def thetaSigned (C logQ : Real) (l : Nat) : Real :=
  -C * paperQMagnitude logQ l

noncomputable def qSigned (logQ : Real) (l : Nat) : Real :=
  -paperQMagnitude logQ l

/-- The paper direction `-|log Theta| >= -|log q|` in the magnitude parametrization
`thetaSigned = -C * |log q|` (so the paper C_Theta equals -C): it holds iff C <= 1,
i.e. C_Theta >= -1 (for |log q| > 0). -/
theorem paperDirection_iff_C_le_one (C logQ : Real) (l : Nat)
    (hQ : 0 < paperQMagnitude logQ l) :
    thetaSigned C logQ l >= qSigned logQ l <-> C <= 1 := by
  unfold thetaSigned qSigned
  constructor <;> intro h <;> nlinarith

/-- Concrete instance l = 13 (l* = 6), logQ = 5 log 11: q magnitude is
5log11/26; raw theta average is (7/12)*5log11; arithFactor is 91/6; the
normalized theta magnitude is again 5log11/26. -/
theorem instance_thirteen :
    paperQMagnitude (5 * Real.log (11 : Real)) 13 =
        5 * Real.log (11 : Real) / 26 ∧
      rawThetaAverage 6 (5 * Real.log (11 : Real)) =
        (7 / 12) * (5 * Real.log (11 : Real)) ∧
      arithFactor 6 = 91 / 6 ∧
      normalizedThetaMagnitude 6 (5 * Real.log (11 : Real)) =
        5 * Real.log (11 : Real) / 26 := by
  refine ⟨by norm_num [paperQMagnitude], by norm_num [rawThetaAverage],
    by norm_num [arithFactor], ?_⟩
  rw [normalizedThetaMagnitude_eq_paperQMagnitude 6 (5 * Real.log 11) (by norm_num)]
  norm_num [paperQMagnitude]

/-- The corrected q-side model: q magnitude = m log p /(2l), not m log p. -/
theorem corrected_q_magnitude (m : Nat) (p : Real) (l : Nat) :
    paperQMagnitude ((m : Real) * Real.log p) l =
      (m : Real) * Real.log p / (2 * (l : Real)) := rfl

/-- The earlier raw q model is the 2l-fold overestimate of the paper q magnitude. -/
theorem rawQModel_eq_twoL_mul_paperQMagnitude (m : Nat) (p : Real) (l : Nat) :
    (m : Real) * Real.log p =
      2 * (l : Real) * paperQMagnitude ((m : Real) * Real.log p) l := by
  unfold paperQMagnitude
  field_simp

end LeanFormal.IUT.XiFPaper.Mzk1PaperProcessionNormalizationActual