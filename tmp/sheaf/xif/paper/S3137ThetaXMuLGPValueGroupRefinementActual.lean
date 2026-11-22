import tmp.sheaf.xif.paper.S3137ThetaXMuLGPRelativeActual
import tmp.sheaf.xif.paper.S3136LGPXMuDegreeActual
import LeanFormal.IUT.Audit.Status

/-!
# S3137: refinement of the theta x mu LGP gap by the actual value-group carrier

IUT III, Definition 3.8, (ii) (pp. 112--113): the Theta x mu LGP-link is a full
poly-isomorphism of F^LGP x mu-prime-strips, which requires both a value-group
(V-double-struck) portion and a unit-group (x mu) portion.

Stage 4 (S3136LGPPhiInputSourceActual / S3136LGPXMuDegreeActual) now provides
the actual value-group portion from the actual q_v/theta data:
* the actual LGP prime index V_bad x {1,...,l*} (IUT III, Prop. 3.4, (ii));
* the free commutative divisor cone on it and the actual prime divisors;
* the actual theta divisor exponents j^2 * ord_v(q_v) and their total-exponent
  (order) homomorphism to N;
* the label-weight law matching FiniteThetaPacket.log_scale
  (IUT II theta-value discussion; Remark 2.5.1, (i)).

This file records that actual value-group refinement, proves the closed
theta-packet log-volume form it implies, and names the exact remaining
unit-group / presentation / full-poly-isomorphism gap.  It does NOT construct
the unit-group (x mu) portion, the local LGP monoids/fractional ideals, or the
Frobenioid isomorphisms of IUT II Cor 4.8(ii) / IUT III Prop 3.7(iv)(v).
No carrier substitution, no value-layer surrogate, no sorry, no axiom.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137ThetaXMuLGPValueGroupRefinementActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S3136LGPPhiInputSourceActual
open LeanFormal.IUT.XiFPaper.S3136LGPXMuDegreeActual
open LeanFormal.IUT.XiFPaper.PaperSymbolTypesActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

universe ua uv upi umon ui
variable {V : Type uv}

/-! ## 1. Actual value-group portion of the F^LGP x mu-prime-strip -/

/-- The actual value-group portion, in one statement: the actual total
theta-divisor exponent (order) homomorphism, its value on each actual LGP prime
divisor, the theta-label weight law matching the FiniteThetaPacket source
log_scale, and positivity of the exponents.  (The bundled actual carrier
LGPXMuCarrier/lgpXMuCarrierActual of stage 4 carries exactly this divisor-side
data; it has no unit-group portion.) -/
theorem lgpValueGroupPortion_actual :
    (∀ p : LGPPrimeIndex (l := l) T,
      lgpThetaDivisorTotalExponent T (lgpThetaPilotPrimeDivisor T p) =
        lgpThetaDivisorExponent T p) ∧
      (∀ (packet : FiniteThetaPacket l) (j : PaperThetaLabel l),
        Real.log (packet.scale j.1) =
          (lgpThetaLabelWeight j : ℝ) * Real.log packet.q) ∧
      (∀ p : LGPPrimeIndex (l := l) T,
        0 < lgpThetaDivisorExponent T p) :=
  ⟨fun p => lgpThetaDivisorTotalExponent_single T p,
    fun packet j => lgpThetaLabelWeight_eq_thetaPacket_log_scale packet j,
    fun p => lgpThetaDivisorExponent_pos T p⟩

theorem lgpThetaDivisorTotalExponent_additive :
    ∀ D E : LGPThetaDivisorCone (l := l) T,
      lgpThetaDivisorTotalExponent T (D + E) =
        lgpThetaDivisorTotalExponent T D + lgpThetaDivisorTotalExponent T E :=
  fun D E => (lgpThetaDivisorTotalExponent T).map_add D E

/-! ## 2. Closed form of the theta-packet log-volume from the label weight -/

/-- The actual theta-packet log-volume is the total gaussian exponent times
log of the packet q (from the proved FiniteThetaPacket.log_scale law, the same
law that stage 4 verifies against the LGP theta-label weights). -/
theorem thetaPacket_logVolume_eq_gauss_sum (packet : FiniteThetaPacket l) :
    packet.logVolume =
      ((∑ j : SignedLabel l.value, (gaussExponent j.1).toNat : ℕ) : ℝ) *
        Real.log packet.q := by
  rw [FiniteThetaPacket.logVolume_eq_sum]
  have hterm : ∀ j : SignedLabel l.value,
      Real.log (packet.scale j) =
        ((gaussExponent j.1).toNat : ℝ) * Real.log packet.q :=
    fun j => FiniteThetaPacket.log_scale packet j
  simp only [hterm]
  rw [← Finset.sum_mul]
  simp only [Nat.cast_sum]

/-! ## 3. Exact remaining LGP gap, refined by the actual value-group data -/

/-- **Exact remaining gap for the Theta x mu LGP-link**, refined by the now
actual value-group portion.  Each field is a source object NOT constructed:

* unitGroupPortion: IUT III, Prop. 3.7, (iv), and Def. 3.8, (ii) -- the
  unit-group (x mu) portion of the F^LGP x mu-prime-strip;
* localLGPMonoids: IUT III, Prop. 3.4, (ii) -- the local LGP-monoids
  Psi_FLGP,v with their label-j components;
* localFractionalIdeals: IUT III, Prop. 3.7, (ii), (v) -- the local fractional
  ideals J_v;
* frobenioidIsomorphisms: IUT II, Cor. 4.8, (ii); IUT III, Prop. 3.7, (i)--(iii)
  -- the Frobenioid isomorphisms transporting C^LGP_gau to C^LGP_LGP;
* firstLGPPresentation: IUT III, Prop. 3.7, (iii) -- the global realified
  LGP-Frobenioid presentation;
* fullPolyIsomorphism: IUT III, Def. 3.8, (ii) -- the full poly-isomorphism of
  F^LGP x mu-prime-strips itself.

The value-group/divisor data (stage 4) is actual and is NOT listed as missing;
nothing else is substituted. -/
structure LGPXMuMissingRefined where
  unitGroupPortion : Prop
  localLGPMonoids : Prop
  localFractionalIdeals : Prop
  frobenioidIsomorphisms : Prop
  firstLGPPresentation : Prop
  fullPolyIsomorphism : Prop

/-- The refined exact gap as a proposition. -/
def LGPXMuMissingRefinedGap : Prop := Nonempty (LGPXMuMissingRefined)

end LeanFormal.IUT.XiFPaper.S3137ThetaXMuLGPValueGroupRefinementActual

namespace LeanFormal.IUT.Audit

/-- **Refined theta x mu LGP gap (value-group side actual).**  The actual
value-group (V-double-struck) portion of the F^LGP x mu-prime-strip is now
constructed from the actual q_v/theta data (divisor cone, prime divisors,
j^2 * ord_v(q_v) exponents, total-exponent homomorphism, label-weight law vs
FiniteThetaPacket.log_scale).  Still missing for IUT III, Definition 3.8, (ii):
the unit-group (x mu) portion, local LGP monoids/fractional ideals, the
Frobenioid isomorphisms of IUT II Cor 4.8(ii), the global realified LGP
presentation, and the full poly-isomorphism of F^LGP x mu-prime-strips. -/
def thetaXMuLGPValueGroupRefined : Obligation :=
  { id := "IUT-III.theta-xmu-LGP-value-group-refined"
    source := "IUT III, Prop. 3.4, (ii), pp. 102-103; Prop. 3.7, (ii)-(v), pp. 108-112; Def. 3.8, (ii), pp. 112-113; IUT II, Cor. 4.8, (ii)"
    status := VerificationStatus.pending
    note := "Value-group (divisor cone/order) portion actual (stage4 S3136LGPPhiInputSourceActual + S3136LGPXMuDegreeActual, consumed here); unit-group (x mu) portion, local LGP monoids/fractional ideals, Frobenioid isomorphisms, realified LGP presentation, and the full poly-isomorphism remain missing.  No carrier substitution."
    dependsOn := ["S3137ThetaXMuLGPRelativeActual", "S3136LGPPhiInputSourceActual", "S3136LGPXMuDegreeActual"] }

end LeanFormal.IUT.Audit