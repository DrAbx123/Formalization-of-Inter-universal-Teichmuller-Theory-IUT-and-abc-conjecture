import tmp.sheaf.xif.paper.S3136LGPPhiInputSourceActual
import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket

/-! # Stage-4 host: LGP value-group (⊩▶) degree layer

The F^LGP×μ-prime-strip of IUT III, Def. 3.8, (ii), requires both a value-group
("⊩▶") portion and a unit-group ("×μ") portion.  This file exposes the actual
value-group/order portion available from the actual q_v/theta data:

* `lgpThetaDivisorTotalExponent`: the order/degree monoid homomorphism from the
  actual LGP theta divisor cone to `ℕ`, summing the actual theta-value divisor
  exponents `j^2 * ord_v(q_v)`;
* `lgpThetaLabelWeight_eq_thetaPacket_log_scale`: the actual gaussian exponent
  `j^2` agrees with the `FiniteThetaPacket` source `log_scale` law
  `log(scale j) = j^2 * log q` (IUT II, theta-value discussion;
  Remark 2.5.1, (i) in the lattice stream's notation).

The unit-group (×μ) portion is NOT constructed here; it remains the exact
object-level gap recorded in `LGPPhiInputSourceMissing` (IUT III, Prop. 3.7,
(iv), (v); Def. 3.8, (ii)). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPXMuDegreeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.LGPPhiInputActual
open LeanFormal.IUT.XiFPaper.LGPPhiInputFromAlgebraicClosureActual
open LeanFormal.IUT.XiFPaper.LGPThetaActionActual
open LeanFormal.IUT.XiFPaper.PaperSymbolTypesActual
open LeanFormal.IUT.XiFPaper.S3136LGPPhiInputSourceActual

universe u

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual theta divisor exponent at the LGP prime (v, j) is the gaussian
exponent j^2 times the actual order of q_v (IUT II, Remark 2.5.1, (i)). -/
theorem lgpThetaDivisorExponent_eq_gauss_mul_order
    (p : LGPPrimeIndex (l := l) T) :
    lgpThetaDivisorExponent T p =
      (gaussExponent p.2.1.1).toNat * lgpQVDivisorExponent T p.1 := rfl

/-- The actual total theta divisor exponent, as an additive homomorphism from
the LGP theta divisor cone to `ℕ`: this is the value-group/order portion of
the F^LGP×μ carrier. -/
noncomputable def lgpThetaDivisorTotalExponent :
    LGPThetaDivisorCone (l := l) T →+ ℕ where
  toFun D := D.sum fun p n => n * lgpThetaDivisorExponent T p
  map_zero' := by
    simp
  map_add' a b := by
    classical
    rw [Finsupp.sum_add_index' (fun p => by simp) (fun p x y => by ring)]

/-- The total theta divisor exponent of a single actual LGP prime divisor is
its actual theta-value divisor exponent. -/
theorem lgpThetaDivisorTotalExponent_single
    (p : LGPPrimeIndex (l := l) T) :
    lgpThetaDivisorTotalExponent T (lgpThetaPilotPrimeDivisor T p) =
      lgpThetaDivisorExponent T p := by
  simp [lgpThetaDivisorTotalExponent, lgpThetaPilotPrimeDivisor]

/-- The actual gaussian exponent j^2 agrees with the `FiniteThetaPacket`
source `log_scale` law: the logarithm of the source theta value at label j is
j^2 times the logarithm of q (IUT II, theta-value discussion). -/
theorem lgpThetaLabelWeight_eq_thetaPacket_log_scale
    (packet : FiniteThetaPacket l) (j : PaperThetaLabel l) :
    Real.log (packet.scale j.1) =
      (lgpThetaLabelWeight j : ℝ) * Real.log packet.q := by
  rw [FiniteThetaPacket.log_scale]
  unfold lgpThetaLabelWeight
  rfl

#check lgpThetaDivisorExponent_eq_gauss_mul_order
#check lgpThetaDivisorTotalExponent
#check lgpThetaDivisorTotalExponent_single
#check lgpThetaLabelWeight_eq_thetaPacket_log_scale

end LeanFormal.IUT.XiFPaper.S3136LGPXMuDegreeActual
end
