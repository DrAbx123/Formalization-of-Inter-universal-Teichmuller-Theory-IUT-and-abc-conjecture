/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A1021: skeleton of the decomposition `M = A + B` (A1020) -/

/- Status: PARTIAL.

Decomposition (A1020, coord/M-POSITIVE-MLINEAR.md):
`M = A + B`, where
* `A = m * log p / (2 l)` is the q-side (positive, m-linear, NOT divided by nC);
* `B` collects the bounded nonnegative terms: after `ind2Term`'s `+j^2*m*logp/(2l)`
  cancels the `scaleElt` `-j^2*m*logp/(2l)` (both are the SAME scaling contribution,
  one inside `V(thetaHull)`, one inside the comparison term), what remains is
  `B = tame + arch + shellDefect + bounded ind2/shell corrections >= 0`.

GAP list (must be closed before this file becomes proof-grade):
* GAP-QROOT: CLOSED (A1022).  lana `ordp_qrootOf` (`Iut/Concrete/ThetaLocalConstruct/Data.lean:327-330`)
  gives `ordp(qroot) = qOrder / (2 * l * ramIdx D.F w)`; for `F = Q` (e_w = 1) this is `m/(2l)`.
* GAP-TENSORVOL: sign of `componentVol_tensorLogShell_eq` (VcI:794 region) and of
  `componentVol_prod_incl_smul_integral` (`componentVol(a * O) = -sum ordp(a_j) log p`).
* GAP-IND2: the exact expansion `ind2Term = V(thetaHull) - V(scaleElt * hull)` with
  `V(thetaHull)` m-independent (contracting scaling, `leastHull_units_smul`/`leastHull_mono`).
* GAP-SOURCES: `tame >= 0` (VcI:435), `archDefect >= 0` (Gap:463), `shellDefect >= 0`
  (Gap:442), `ind2Term >= 0` (Gap:756) are green-by-source; their sum into B needs the
  exact packet expansion (LogVolume:130-133) and the `1/nC` placement (DECOMP-NORMALIZATION).

Circularity: `B_nonneg` must be proved from the green nonnegative local terms, NOT from
`M >= 0`, `SSIneq`, `Corollary312Variant`, or `PaperNormVerdict`.  This skeleton keeps `B`
abstract with a nonnegativity field; filling it is the remaining work.
No sorry/axiom.  Written for watchdog compilation only (no manual compile). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1MDecompositionActual

open Finset

/-- Abstract decomposition data for `M = A + B`. -/
structure MDecompositionData where
  m : Real
  logp : Real
  l : Real
  m_nonneg : 0 <= m
  logp_pos : 0 < logp
  l_pos : 0 < l
  B : Real
  B_nonneg : 0 <= B

/-- The q-side `A = m * log p / (2 l)` (no 1/nC; LeftHandSide:81-88). -/
noncomputable def AOf (D : MDecompositionData) : Real :=
  D.m * D.logp / (2 * D.l)

/-- `M = A + B`. -/
noncomputable def MOf (D : MDecompositionData) : Real :=
  AOf D + D.B

/-- Definitional split `M = A + B`. -/
theorem M_eq_A_add_B (D : MDecompositionData) : MOf D = AOf D + D.B :=
  rfl

/-- `A >= 0` from the data. -/
theorem AOf_nonneg (D : MDecompositionData) : 0 <= AOf D := by
  unfold AOf
  apply div_nonneg
  · exact mul_nonneg D.m_nonneg D.logp_pos.le
  · exact mul_nonneg (by norm_num) D.l_pos.le

/-- **Decomposition theorem**: `M = A + B >= 0` from `A >= 0` and `B >= 0`. -/
theorem M_nonneg_of_decomposition (D : MDecompositionData) : 0 <= MOf D := by
  rw [M_eq_A_add_B]
  exact add_nonneg (AOf_nonneg D) D.B_nonneg

/-- The m-linear coefficient of the q-side: `dA/dm = log p / (2 l) > 0` (A1020). -/
noncomputable def dAdm (D : MDecompositionData) : Real :=
  D.logp / (2 * D.l)

theorem dAdm_pos (D : MDecompositionData) : 0 < dAdm D := by
  unfold dAdm
  apply div_pos D.logp_pos
  exact mul_pos (by norm_num) D.l_pos

/-- GAP-QROOT closed: normalization `qOrder/(2l*ramIdx)` (lana `ordp_qrootOf`). -/
theorem ordpQroot_eq (qOrder l ramIdx : Real) (hl : 0 < l) (hr : 0 < ramIdx) :
    qOrder / (2 * l) / ramIdx = qOrder / (2 * l * ramIdx) := by
  field_simp [hl.ne', hr.ne']

/-- Abstract scaling-volume term (source: `componentVol_units_smul`, IdentifiedCopies:67;
`scaleElt = qroot^{j^2}`, ThetaRegion:126-139). -/
def scaleVol (j m logp l : Real) : Real :=
  - (j ^ 2) * m * logp / (2 * l)

/-- Abstract ind2 leading term (source: `ind2Term`, Gap:747-756). -/
def ind2Leading (j m logp l : Real) : Real :=
  (j ^ 2) * m * logp / (2 * l)

/-- Arithmetic core of A1020: the scaling negative term and the ind2 positive term cancel. -/
theorem scaleVol_add_ind2Leading (j m logp l : Real) :
    scaleVol j m logp l + ind2Leading j m logp l = 0 := by
  unfold scaleVol ind2Leading
  ring

/-- The A-side m-linear coefficient after the cancellation is `+log p/(2 l)`. -/
theorem net_mLine_after_cancel (D : MDecompositionData) :
    dAdm D + scaleVol 1 D.m D.logp D.l + ind2Leading 1 D.m D.logp D.l = dAdm D := by
  have h := scaleVol_add_ind2Leading 1 D.m D.logp D.l
  linarith

def mDecompositionRows : List (String × String) :=
  [ ("M = A + B", "A q-side; B bounded nonnegative") ,
    ("AOf", "m*logp/(2l), no 1/nC (LeftHandSide:81-88)") ,
    ("dAdm_pos", "dA/dm = logp/(2l) > 0 (A1020)") ,
    ("scaleVol + ind2Leading = 0", "j^2 scaling cancels (pure arithmetic, A1020)") ,
    ("GAP-QROOT", "ordp(qroot) = m/(2l) (InitialData.qroot)") ,
    ("GAP-TENSORVOL", "componentVol_tensorLogShell_eq sign (VcI:794)") ,
    ("GAP-IND2", "V(thetaHull) m-independent; ind2 exact expansion (Gap:747-756)") ,
    ("GAP-SOURCES", "tame/arch/shellDefect/ind2 nonneg sources (green-by-source)") ]

theorem mDecompositionRows_length : mDecompositionRows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1MDecompositionActual