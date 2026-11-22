import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # S700: 2l-normalized theta values from the q-parameter q[1u]

CRITICAL normalization correction.  Existing FiniteThetaPacket.ofQ uses
realThetaValue q j = q^(j^2), which treats q as the double-underlined 2l-th
root q[2u].  The actual C3.q is the single-underlined q-parameter q[1u], so the
paper theta value is

  q[2u]^(j^2) = q[1u]^(j^2/(2l)).

This file defines the corrected real theta value and a corrected finite packet.
It does not assert any comparison using the old (missing 2l) scaling. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S700ThetaQParameterNormalizationActual

open LeanFormal.IUT

universe u

/-- Corrected theta value from the q-parameter q[1u]:
q[1u]^(j^2/(2l)). -/
noncomputable def qParameterThetaValue
    (l : PrimeGeFive) (q : Real) (j : Int) : Real :=
  q ^ (((j ^ 2 : Int) : Real) / (2 * (l.value : Real)))

theorem qParameterThetaValue_eq_rpow
    (l : PrimeGeFive) (q : Real) (j : Int) :
    qParameterThetaValue l q j =
      q ^ (((j ^ 2 : Int) : Real) / (2 * (l.value : Real))) := rfl

theorem qParameterThetaValue_pos
    (l : PrimeGeFive) {q : Real} (hq : 0 < q) (j : Int) :
    0 < qParameterThetaValue l q j := by
  unfold qParameterThetaValue
  exact Real.rpow_pos_of_pos hq _

theorem log_qParameterThetaValue
    (l : PrimeGeFive) {q : Real} (hq : 0 < q) (j : Int) :
    Real.log (qParameterThetaValue l q j) =
      (((j ^ 2 : Int) : Real) / (2 * (l.value : Real))) * Real.log q := by
  unfold qParameterThetaValue
  rw [Real.log_rpow hq]

/-- Corrected finite theta packet using q[1u] and the 1/(2l) exponent. -/
structure FiniteThetaPacketQParameter (l : PrimeGeFive) where
  q : Real
  q_pos : 0 < q
  scale : SignedLabel l.value → Real
  scale_eq : ∀ j, scale j = qParameterThetaValue l q j.1

namespace FiniteThetaPacketQParameter

variable {l : PrimeGeFive}

noncomputable def ofQParameter (q : Real) (hq : 0 < q) :
    FiniteThetaPacketQParameter l where
  q := q
  q_pos := hq
  scale := fun j => qParameterThetaValue l q j.1
  scale_eq := by intro j; rfl

theorem scale_pos (packet : FiniteThetaPacketQParameter l)
    (j : SignedLabel l.value) : 0 < packet.scale j := by
  rw [packet.scale_eq]
  exact qParameterThetaValue_pos l packet.q_pos j.1

theorem log_scale (packet : FiniteThetaPacketQParameter l)
    (j : SignedLabel l.value) :
    Real.log (packet.scale j) =
      (((j.1 ^ 2 : Int) : Real) / (2 * (l.value : Real))) *
        Real.log packet.q := by
  rw [packet.scale_eq, log_qParameterThetaValue l packet.q_pos]

end FiniteThetaPacketQParameter

end LeanFormal.IUT.XiFPaper.S700ThetaQParameterNormalizationActual

end
