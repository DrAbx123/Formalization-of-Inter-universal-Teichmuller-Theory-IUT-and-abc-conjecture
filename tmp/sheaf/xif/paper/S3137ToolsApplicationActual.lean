import tmp.sheaf.xif.paper.S3137LogVolumeMapToolActual
import tmp.sheaf.xif.paper.S3137PadicNormToolActual
import tmp.sheaf.xif.paper.S3137ThetaPacketLogVolumeToolActual

/-!
# S3137: APPLICATIONS of the manufactured tools

Applications of the generic tools to the actual q-pilot / theta-packet reading
shapes.  These are the concrete instances that consumers (Hull Theta-half, LGP
q_v readings, q-pilot signed readouts) can cite directly:

* `log_padic_norm_five` / `signedReading_padic_five`: the five-adic norm of 5 is
  1/5, so the signed q-pilot reading is `log 5` (q = 1/5);
* `thetaPacket_ofQ_inv_five_logVolume`: the Gaussian packet with q = 1/5 has
  log-volume `(∑ gauss weight) * log(1/5) = -(∑ gauss weight) * log 5` (the
  negative `-|log q|` shape), by the generic packet closed form.

Source: IUT I, Example 3.2, (iv); IUT II, Remark 2.5.1, (i); IUT III, Def.
3.8, (i), p. 112; Prop. 3.9, (i), p. 115.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.ToolsApplicationActual

local instance factPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.PadicNormToolActual
open LeanFormal.IUT.XiFPaper.ThetaPacketLogVolumeToolActual

/-- Application of the padic-norm tool: the logarithmic norm of the five-adic
scalar 5 is `-log 5`. -/
theorem log_padic_norm_five : Real.log ‖(5 : ℚ_[5])‖ = -Real.log 5 := by
  rw [padic_norm_five, Real.log_inv]

/-- Application: the signed q-pilot reading for q = 1/5 is `log 5` (the
`-|log q|` shape used in the q/Theta comparison). -/
theorem signedReading_padic_five : -Real.log ‖(5 : ℚ_[5])‖ = Real.log 5 := by
  rw [log_padic_norm_five, neg_neg]

/-- Application of the theta-packet tool: the Gaussian packet with q = 1/5 has
log-volume `(∑ gauss weight) * log(1/5)`. -/
theorem thetaPacket_ofQ_inv_five_logVolume (l : PrimeGeFive) :
    (FiniteThetaPacket.ofQ (l := l) ((5 : ℝ)⁻¹) (by norm_num)).logVolume =
      (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : ℝ)) *
        Real.log ((5 : ℝ)⁻¹) :=
  finiteThetaPacket_logVolume_ofQ_eq (l := l) ((5 : ℝ)⁻¹) (by norm_num)

/-- Application: the same log-volume in the `-|log q|` shape,
`-(∑ gauss weight) * log 5`. -/
theorem thetaPacket_ofQ_inv_five_logVolume_neg_shape (l : PrimeGeFive) :
    (FiniteThetaPacket.ofQ (l := l) ((5 : ℝ)⁻¹) (by norm_num)).logVolume =
      -((∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : ℝ)) *
        Real.log 5) := by
  rw [thetaPacket_ofQ_inv_five_logVolume, Real.log_inv]
  ring

end LeanFormal.IUT.XiFPaper.ToolsApplicationActual