/-
  Reduction pass: the arithmetic realization of the Theta-link displacement
  `n Theta_v |-> (n+1) q_v` (Remark 3.8.1 (i), Fig. 3.1 of IUT I).

  Paper anchors (`D:\lean\papers\motizuki_corpus\text\Inter-universal
  Teichmuller Theory I.txt`):

  * Remark 3.8.1 (i), lines 5067--5087: "the Theta-link maps
    n Theta_v |-> (n+1) q_v [i.e., where v in V_bad]"; in Fig. 3.1 "each box
    is a Theta-Hodge theater", the dashed arrow "----" is the Theta-link,
    and the "~>" denotes "the scheme theory that lies between q_v and
    Theta_v".
  * Remark 3.8.1 (ii), lines 5088--5096: "the Frobenius-picture involves, in
    an essential way, the divisor monoid portion [i.e., "q_v" and "Theta_v"]
    of the various Frobenioids that appear in a Theta-Hodge theater".

  Frozen obligation addressed by this file (new in this pass):
  `IUT-I.theta-link-arithmetic-displacement-reduction`.  It continues the
  reduction list of `SourceThetaLinkDisplacementReduction.lean` (card C2b:
  the arithmetic realization of the displacement) and does not touch the
  frozen companion files.

  Proved in this file:

  1. For every `HodgeTheaterLink A B`, the theta-side special values of the
     *source* are the Gaussian evaluations of the *target* q-parameter:
     `A.scale j = realThetaValue B.q j` -- the finite-model realization of
     the displacement "n Theta_v |-> (n+1) q_v" (value form), together with
     the symmetric reading (the link identifies the two q-sides, so both
     readings hold in this carrier).
  2. The logarithmic (additive) form: the log of the source theta-side value
     is the Gaussian exponent weight times the log of the target
     q-parameter; the product and log-volume forms.
  3. Composite (two-link) and chain-wide versions on a
     `SourceThetaLinkChain`: the source theta-side at any node is the
     Gaussian evaluation of the q-parameter at any other node.
  4. Concrete arithmetic instance on the q = 5 local Kummer carrier: the
     log-forms equal the documented Gaussian weights times the actual local
     norm-degree `localUnitNormDegreeFor 5 (localQParameterFor 5)`, and the
     same read holds through the concrete three-theater system.  The
     non-triviality of the transported q at the divisor-monoid layer is the
     already-proved `LocalIntegralMonoid.qParameterGroupification_ne_one 5`
     (cited from the concrete carrier, not reproved here).

  Reductions (explicitly marked; none of these is the original statement):

  * The scheme theory "~>" between q_v and Theta_v is *not* modeled: the
    repository has no scheme-theoretic or Frobenioid comparison object for
    it.  The finite Gaussian evaluation `j |-> q ^ (j^2)` of the existing
    `FiniteThetaPacket` stands in for the comparison (marked as such).
  * The link equalizes q across a link, so in this carrier the paper's
    directional comparison "Theta-side of n versus q-side of n+1" is
    realized only up to this collapse; both readings (target and source
    q-parameter) are provable and recorded.
  * The concrete instance is the single finite place p = 5 with the Gaussian
    arithmetic; the general bad-place frobenioid arithmetic (divisor
    monoids of the Frobenioids, as in Remark 3.8.1 (ii)) remains card C2b.
  * The finite packet is not identified with the source's etale theta
    function (following the existing `FiniteThetaPacket` boundary).

  Consumers: D3.1 (`IUTIII\Theorem311\SourceOriginalInput.lean:41-46`),
  Theorem 3.11 source chain
  (`IUTIII\Theorem311\SourceH1H2Construction.lean:272-277`), and
  `SourceHodgeTheaterBridge`.
-/

import LeanFormal.IUT.IUTI.HodgeTheater.SourceThetaLinkDisplacementReduction
import LeanFormal.IUT.IUTI.HodgeTheater.ConcreteIntegralHodgeTheaterExample

set_option linter.checkUnivs false

namespace LeanFormal.IUT

noncomputable section

universe ua uv upi umon

local instance fivePrimeFactArithmeticDisplacement : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

variable {l : PrimeGeFive} {V : Type uv}

/-! ## 1. The one-step arithmetic realization of the displacement -/

/-- The finite-model realization of `n Theta_v |-> (n+1) q_v`: the
theta-side special values of the source are the Gaussian evaluations of the
target q-parameter. -/
theorem thetaSide_eq_gaussian_of_target_q
    {A B : HodgeTheater.{ua, uv, upi, umon} l V} (L : HodgeTheaterLink A B)
    (j : SignedLabel l.value) :
    A.thetaPacket.scale j = realThetaValue B.thetaPacket.q j.1 := by
  rw [A.thetaPacket.scale_eq j, L.theta_q_eq]

/-- Symmetric reading: the link identifies the q-sides, so the target
theta-side is also the Gaussian evaluation of the source q-parameter. -/
theorem thetaSide_eq_gaussian_of_source_q
    {A B : HodgeTheater.{ua, uv, upi, umon} l V} (L : HodgeTheaterLink A B)
    (j : SignedLabel l.value) :
    B.thetaPacket.scale j = realThetaValue A.thetaPacket.q j.1 := by
  rw [B.thetaPacket.scale_eq j, L.theta_q_eq.symm]

/-- The additive (log) form of the displacement: the log of the transported
theta-side value is the Gaussian exponent weight times the log of the target
q-parameter. -/
theorem log_thetaSide_eq_gaussExponent_mul_target_log_q
    {A B : HodgeTheater.{ua, uv, upi, umon} l V} (L : HodgeTheaterLink A B)
    (j : SignedLabel l.value) :
    Real.log (A.thetaPacket.scale j) =
      (gaussExponent j.1).toNat * Real.log B.thetaPacket.q := by
  rw [thetaSide_eq_gaussian_of_target_q L j, log_realThetaValue]

/-- Product form of the displacement. -/
theorem packet_scale_product_eq_prod_gaussian_of_target_q
    {A B : HodgeTheater.{ua, uv, upi, umon} l V} (L : HodgeTheaterLink A B) :
    (∏ j : SignedLabel l.value, A.thetaPacket.scale j) =
      ∏ j : SignedLabel l.value, realThetaValue B.thetaPacket.q j.1 := by
  apply Finset.prod_congr rfl
  intro j hj
  exact thetaSide_eq_gaussian_of_target_q L j

/-- Log-volume form of the displacement: the whole source log-volume is the
Gaussian weighted sum of the log of the target q-parameter. -/
theorem packet_logVolume_eq_sum_gaussExponent_of_target_q
    {A B : HodgeTheater.{ua, uv, upi, umon} l V} (L : HodgeTheaterLink A B) :
    A.thetaPacket.logVolume =
      ∑ j : SignedLabel l.value,
        (gaussExponent j.1).toNat * Real.log B.thetaPacket.q := by
  rw [A.thetaPacket.logVolume_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact log_thetaSide_eq_gaussExponent_mul_target_log_q L j

/-- Composite (two-link) form of the displacement. -/
theorem thetaSide_eq_gaussian_of_composite
    {A B C : HodgeTheater.{ua, uv, upi, umon} l V}
    (L₁ : HodgeTheaterLink A B) (L₂ : HodgeTheaterLink B C)
    (j : SignedLabel l.value) :
    A.thetaPacket.scale j = realThetaValue C.thetaPacket.q j.1 :=
  thetaSide_eq_gaussian_of_target_q (L₁.trans L₂) j

/-! ## 2. Chain-wide forms on a Frobenius-picture chain -/

namespace SourceThetaLinkChain

variable {l : PrimeGeFive} {V : Type uv}

/-- One-step form on the chain: the theta-side at n is the Gaussian
evaluation of the q-parameter at n+1. -/
theorem thetaSide_eq_gaussian_of_step
    (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) (n : Int)
    (j : SignedLabel l.value) :
    (C.theater n).thetaPacket.scale j =
      realThetaValue (C.theater (n + 1)).thetaPacket.q j.1 :=
  thetaSide_eq_gaussian_of_target_q (C.step n) j

/-- Chain-wide form: the theta-side at any node is the Gaussian evaluation of
the q-parameter at any other node (the q-parameter is constant along the
chain by the displacement laws of the companion file). -/
theorem thetaSide_eq_gaussian_any
    (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) (m n : Int)
    (j : SignedLabel l.value) :
    (C.theater m).thetaPacket.scale j =
      realThetaValue (C.theater n).thetaPacket.q j.1 := by
  rw [(C.theater m).thetaPacket.scale_eq j, C.thetaQ_eq m n]

/-- Chain-wide log-volume form. -/
theorem logVolume_eq_sum_gaussExponent_any
    (C : SourceThetaLinkChain.{ua, uv, upi, umon} l V) (m n : Int) :
    (C.theater m).thetaPacket.logVolume =
      ∑ j : SignedLabel l.value,
        (gaussExponent j.1).toNat * Real.log (C.theater n).thetaPacket.q := by
  rw [(C.theater m).thetaPacket.logVolume_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [(C.theater m).thetaPacket.scale_eq j, C.thetaQ_eq m n, log_realThetaValue]

end SourceThetaLinkChain

/-! ## 3. Concrete arithmetic instance on the q = 5 local carrier -/

/-- Per-slot log identity on the concrete integral carrier: the log of each
theta-side value is the Gaussian weight times the actual local norm-degree of
the q = 5 Kummer unit. -/
theorem gaussianFiniteIntegralHodgeTheater_log_scale
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    Real.log ((gaussianFiniteIntegralHodgeTheater l).thetaPacket.scale j) =
      (gaussExponent j.1).toNat *
        Multiplicative.toAdd (localUnitNormDegreeFor 5 (localQParameterFor 5)) := by
  rw [(gaussianFiniteIntegralHodgeTheater l).thetaPacket.log_scale j,
    gaussianFiniteIntegralHodgeTheater_q, gaussianFiveThetaQ_log_eq_local_degree]

/-- The displacement realized on the concrete three-theater system: the
theta-side of the source is the Gaussian evaluation of the target
q-parameter (the target q is the q = 5 carrier). -/
theorem gaussianFiniteIntegralThreeTheaterSystem_theta_side
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    (gaussianFiniteIntegralThreeTheaterSystem l).source.thetaPacket.scale j =
      realThetaValue
        (gaussianFiniteIntegralThreeTheaterSystem l).target.thetaPacket.q j.1 :=
  thetaSide_eq_gaussian_of_target_q
    (gaussianFiniteIntegralThreeTheaterSystem l).sourceToTarget j

/-- Directed log-form on the concrete system: the log of the source
theta-side value is the Gaussian weight times the local norm-degree of the
q = 5 carrier. -/
theorem gaussianFiniteIntegralThreeTheaterSystem_source_log_scale_local_degree
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    Real.log ((gaussianFiniteIntegralThreeTheaterSystem l).source.thetaPacket.scale j) =
      (gaussExponent j.1).toNat *
        Multiplicative.toAdd (localUnitNormDegreeFor 5 (localQParameterFor 5)) := by
  have hq : (gaussianFiniteIntegralThreeTheaterSystem l).target.thetaPacket.q =
      gaussianFiveThetaQ :=
    gaussianFiniteIntegralHodgeTheater_q l
  rw [log_thetaSide_eq_gaussExponent_mul_target_log_q
    (gaussianFiniteIntegralThreeTheaterSystem l).sourceToTarget j,
    hq, gaussianFiveThetaQ_log_eq_local_degree]

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def thetaLinkArithmeticDisplacementReduction : Obligation :=
  { id := "IUT-I.theta-link-arithmetic-displacement-reduction"
    source :=
      "IUT I: Remark 3.8.1, (i) (the Theta-link maps n Theta_v |-> (n+1) " ++
        "q_v; Fig. 3.1) and (ii) (the divisor monoid portion, i.e., q_v " ++
        "and Theta_v, of the Frobenioids in a Theta-Hodge theater)"
    status := VerificationStatus.interface
    note :=
      "Reduction pass for the arithmetic realization of the displacement. " ++
        "Proved here: for every HodgeTheaterLink, the source theta-side " ++
        "values are the Gaussian evaluations of the target q-parameter " ++
        "(value, log, product and log-volume forms), with composite and " ++
        "chain-wide versions; on the concrete q = 5 local carrier the log " ++
        "forms equal the documented Gaussian weights times the actual " ++
        "local norm-degree. Reductions: the scheme theory between q_v and " ++
        "Theta_v (Fig. 3.1) is not modeled; the finite Gaussian evaluation " ++
        "of the packet stands in for it. The link equalizes the q-side, so " ++
        "the paper's directional comparison is realized only up to this " ++
        "collapse. The general frobenioid divisor-monoid realization " ++
        "remains card C2b; the concrete instance is the single finite " ++
        "place 5."
    dependsOn :=
      [ "IUT-I.theta-link-displacement-reduction",
        "IUT-I.hodge-theater-carrier-and-links",
        "IUT-I-II.concrete-finite-integral-hodge-carrier",
        "IUT-II.finite-theta-packet" ] }

end LeanFormal.IUT.Audit
