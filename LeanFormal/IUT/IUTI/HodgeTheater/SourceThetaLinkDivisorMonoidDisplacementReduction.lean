/-
  Reduction pass: the Theta-link displacement at the frobenioid divisor-monoid
  layer, for the general prime family (IUT I, Remark 3.8.1 (i) and (ii)).

  Paper anchors (`D:\lean\papers\motizuki_corpus\text\Inter-universal
  Teichmuller Theory I.txt`):

  * Remark 3.8.1 (i), lines 5067--5087: "the Theta-link maps
    n Theta_v |-> (n+1) q_v [i.e., where v in V_bad]"; in Fig. 3.1 the dashed
    arrow "----" is the Theta-link and "~>" denotes "the scheme theory that
    lies between q_v and Theta_v".
  * Remark 3.8.1 (ii), lines 5088--5096: "the Frobenius-picture involves, in
    an essential way, the divisor monoid portion [i.e., q_v and Theta_v] of
    the various Frobenioids that appear in a Theta-Hodge theater".

  Frozen proposition carried by this file (the general layer of card C2b;
  the general-linked value layer is the frozen companion file
  `SourceThetaLinkArithmeticDisplacementReduction`):

  * For every rational prime p (the general bad place, through the local
    p-adic carrier) and every l : PrimeGeFive:
    - the divisor-monoid portion element `qParameter p` of the nonzero
      integral-closure monoid has norm-log degree `- log p`; the same value
      holds for its Grothendieck groupification element; both are nontrivial
      for every prime (removing the single-prime restriction of the
      q = 5 pass);
    - the finite carrier with q-value `primeThetaQ p = ‖localQParameterFor p‖`
      satisfies the Gaussian displacement laws, with the log-form written
      through the divisor-monoid degree.
  * For every finite place v of the prime strip [2,7] (the finite-interval
    model of the paper's bad-prime set): the strip degree of the local
    q-parameter obeys the same norm-log law, and every F-prime-strip
    equivalence (in particular the prime-strip part of any HodgeTheaterLink
    between carrier-level theaters) preserves this displacement value.
  * Model layer (route reuse): the divisor-monoid portion of the packaged
    model Frobenioid at the concrete Gaussian place has Grothendieck
    groupification canonically Z; the bridge carrying the local q-parameter
    into that model is not constructed (card C2b-general).

  Reductions (explicitly marked; none of these is the original statement):

  * The paper's "divisor monoid portion of the various Frobenioids" is here
    modeled by the nonzero integral-closure monoid `LocalIntegralMonoid p`
    and its groupification (the audited IUT II, Definition 4.9(i) carrier).
    The model Frobenioid divisor monoid of the finite-stage reconstruction
    lives on the Gaussian-field side and is not connected to the local
    p-adic q-parameter; that bridge is missing and is card C2b-general.
  * The scheme-theoretic "~>" between q_v and Theta_v stays PARKED (no
    scheme/Frobenioid comparison object in the repository).
  * The Gaussian evaluation j |-> q ^ (j^2) of the finite packet stands in
    for the theta comparison, as in the frozen companion files.
  * General-link generality at the value layer is not reproved here: the
    frozen `thetaSide_eq_gaussian_of_target_q` (arbitrary HodgeTheaterLink,
    arbitrary q) already covers it.

  Consumers: D3.1 (`IUTIII\Theorem311\SourceOriginalInput.lean:41-46`),
  Theorem 3.11 source chain
  (`IUTIII\Theorem311\SourceH1H2Construction.lean:272-277`), and
  `SourceHodgeTheaterBridge`.
-/

import LeanFormal.IUT.IUTI.HodgeTheater.SourceThetaLinkArithmeticDisplacementReduction
import LeanFormal.IUT.IUTII.Frobenioid.LocalIntegralFPrimeStrip
import LeanFormal.IUT.IUTII.Frobenioid.ConcreteSourceFrobenioidBridge

set_option linter.checkUnivs false

namespace LeanFormal.IUT

noncomputable section

universe ua uv upi umon

local instance fivePrimeFactDivisorMonoid : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-! ## 1. The general-prime displacement value (removing the single prime 5) -/

/-- The general-prime theta q-value: the norm of the local q-parameter
`q_p = p` in the algebraic closure of `Q_p`. -/
noncomputable def primeThetaQ (p : Nat) [Fact (Nat.Prime p)] : Real :=
  ‖(localQParameterFor p : AlgebraicClosure ℚ_[p])‖

theorem primeThetaQ_pos (p : Nat) [Fact (Nat.Prime p)] :
    0 < primeThetaQ p :=
  norm_pos_unit (AlgebraicClosure ℚ_[p]) (localQParameterFor p)

theorem primeThetaQ_eq_exp_local_degree (p : Nat) [Fact (Nat.Prime p)] :
    primeThetaQ p =
      Real.exp (Multiplicative.toAdd
        (localUnitNormDegreeFor p (localQParameterFor p))) := by
  change ‖(localQParameterFor p : AlgebraicClosure ℚ_[p])‖ =
    Real.exp (Real.log ‖(localQParameterFor p : AlgebraicClosure ℚ_[p])‖)
  exact (Real.exp_log (primeThetaQ_pos p)).symm

theorem primeThetaQ_log_eq_local_degree (p : Nat) [Fact (Nat.Prime p)] :
    Real.log (primeThetaQ p) =
      Multiplicative.toAdd
        (localUnitNormDegreeFor p (localQParameterFor p)) := by
  rw [primeThetaQ_eq_exp_local_degree, Real.log_exp]

/-- Consistency with the frozen q = 5 pass. -/
theorem primeThetaQ_five_eq_gaussianFiveThetaQ :
    primeThetaQ 5 = gaussianFiveThetaQ := rfl

/-! ## 2. The displacement arithmetic at the divisor-monoid portion -/

/-- The q-parameter of the divisor-monoid portion (the nonzero integral
closure monoid) has the same norm-log degree as its ambient unit. -/
theorem qParameter_localIntegralNormDegree_apply (p : Nat) [Fact (Nat.Prime p)] :
    localIntegralNormDegreeFor p (LocalIntegralMonoid.qParameter p) =
      localUnitNormDegreeFor p (localQParameterFor p) := by
  change localUnitNormDegreeFor p
    (LocalIntegralMonoid.toAlgebraicClosureUnits p
      (LocalIntegralMonoid.qParameter p)) =
    localUnitNormDegreeFor p (localQParameterFor p)
  rw [LocalIntegralMonoid.toAlgebraicClosureUnits_qParameter]

/-- The q-parameter's value at the algebraic-closure layer: norm `1/p`
(Mathlib `PadicAlgCl.valuation_p`). -/
theorem localQParameterFor_norm_eq_inv (p : Nat) [Fact (Nat.Prime p)] :
    ‖(localQParameterFor p : AlgebraicClosure ℚ_[p])‖ = (p : ℝ)⁻¹ := by
  have hval := PadicAlgCl.valuation_p p
  calc ‖(localQParameterFor p : AlgebraicClosure ℚ_[p])‖
      = ((Valued.v (localQParameterFor p : AlgebraicClosure ℚ_[p]) : NNReal) : ℝ) :=
        (PadicAlgCl.valuation_coe p (localQParameterFor p : AlgebraicClosure ℚ_[p])).symm
    _ = ((Valued.v (p : PadicAlgCl p) : NNReal) : ℝ) := rfl
    _ = ((1 / (p : NNReal) : NNReal) : ℝ) := by rw [hval]
    _ = (p : ℝ)⁻¹ := by
        push_cast
        rw [one_div]

theorem localUnitNormDegreeFor_localQParameter_toAdd
    (p : Nat) [Fact (Nat.Prime p)] :
    Multiplicative.toAdd (localUnitNormDegreeFor p (localQParameterFor p)) =
      - Real.log (p : ℝ) := by
  change Real.log ‖(localQParameterFor p : AlgebraicClosure ℚ_[p])‖ =
    - Real.log (p : ℝ)
  rw [localQParameterFor_norm_eq_inv, Real.log_inv]

/-- The displacement degree of the divisor-monoid q-parameter is `- log p`
for every prime. -/
theorem qParameter_localIntegralNormDegree_toAdd
    (p : Nat) [Fact (Nat.Prime p)] :
    Multiplicative.toAdd
      (localIntegralNormDegreeFor p (LocalIntegralMonoid.qParameter p)) =
      - Real.log (p : ℝ) := by
  rw [qParameter_localIntegralNormDegree_apply,
    localUnitNormDegreeFor_localQParameter_toAdd]

theorem primeThetaQ_log_eq_qParameter_degree
    (p : Nat) [Fact (Nat.Prime p)] :
    Real.log (primeThetaQ p) =
      Multiplicative.toAdd
        (localIntegralNormDegreeFor p (LocalIntegralMonoid.qParameter p)) := by
  rw [primeThetaQ_log_eq_local_degree,
    ← qParameter_localIntegralNormDegree_apply]

/-- The displacement degree `- log p` is nonzero for every prime. -/
theorem neg_log_prime_ne_zero (p : Nat) [Fact (Nat.Prime p)] :
    - Real.log (p : ℝ) ≠ 0 := by
  intro h
  have hlog : Real.log (p : ℝ) = 0 := by linarith
  have hp : Nat.Prime p := Fact.out
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_ne_one : (p : ℝ) ≠ 1 := by
    intro h1
    exact hp.ne_one (by exact_mod_cast h1)
  exact (Real.log_ne_zero_of_pos_of_ne_one hp_pos hp_ne_one) hlog

/-- Nontriviality of the displacement value at the divisor-monoid portion:
the q-parameter's degree is not 1, for every prime. -/
theorem qParameter_localIntegralNormDegree_ne_one
    (p : Nat) [Fact (Nat.Prime p)] :
    localIntegralNormDegreeFor p (LocalIntegralMonoid.qParameter p) ≠ 1 := by
  intro h
  apply neg_log_prime_ne_zero p
  rw [← qParameter_localIntegralNormDegree_toAdd, h]
  simp

/-- Powers of the divisor-monoid q-parameter scale the displacement degree
linearly (the index-shift arithmetic), for every prime. -/
theorem qParameter_localIntegralNormDegree_pow_toAdd
    (p : Nat) [Fact (Nat.Prime p)] (k : ℕ) :
    Multiplicative.toAdd
      (localIntegralNormDegreeFor p (LocalIntegralMonoid.qParameter p ^ k)) =
      k * (- Real.log (p : ℝ)) := by
  rw [map_pow, toAdd_pow,
    qParameter_localIntegralNormDegree_toAdd]
  exact nsmul_eq_mul k _

/-- The degree of the divisor-monoid portion transported to the Grothendieck
groupification. -/
noncomputable def divisorMonoidGroupDegree (p : Nat) [Fact (Nat.Prime p)] :
    Algebra.GrothendieckGroup (LocalIntegralMonoid p) →* Multiplicative Real :=
  (localUnitNormDegreeFor p).comp
    (LocalIntegralMonoid.groupificationToAlgebraicClosureUnits p)

theorem divisorMonoidGroupDegree_qParameterGroupification
    (p : Nat) [Fact (Nat.Prime p)] :
    divisorMonoidGroupDegree p (LocalIntegralMonoid.qParameterGroupification p) =
      localUnitNormDegreeFor p (localQParameterFor p) := by
  change localUnitNormDegreeFor p
    (LocalIntegralMonoid.groupificationToAlgebraicClosureUnits p
      (Algebra.GrothendieckGroup.of (LocalIntegralMonoid.qParameter p))) =
    localUnitNormDegreeFor p (localQParameterFor p)
  rw [LocalIntegralMonoid.groupificationToAlgebraicClosureUnits_of,
    LocalIntegralMonoid.toAlgebraicClosureUnits_qParameter]

theorem divisorMonoidGroupDegree_qParameterGroupification_toAdd
    (p : Nat) [Fact (Nat.Prime p)] :
    Multiplicative.toAdd
      (divisorMonoidGroupDegree p
        (LocalIntegralMonoid.qParameterGroupification p)) =
      - Real.log (p : ℝ) := by
  rw [divisorMonoidGroupDegree_qParameterGroupification,
    localUnitNormDegreeFor_localQParameter_toAdd]

theorem divisorMonoidGroupDegree_qParameterGroupification_ne_one
    (p : Nat) [Fact (Nat.Prime p)] :
    divisorMonoidGroupDegree p
      (LocalIntegralMonoid.qParameterGroupification p) ≠ 1 := by
  intro h
  apply neg_log_prime_ne_zero p
  rw [← divisorMonoidGroupDegree_qParameterGroupification_toAdd, h]
  simp

/-- Integer powers of the groupification class scale the displacement degree
linearly (the Z-index shift arithmetic), for every prime. -/
theorem divisorMonoidGroupDegree_qParameterGroupification_zpow_toAdd
    (p : Nat) [Fact (Nat.Prime p)] (z : ℤ) :
    Multiplicative.toAdd
      (divisorMonoidGroupDegree p
        (LocalIntegralMonoid.qParameterGroupification p ^ z)) =
      z • (- Real.log (p : ℝ)) := by
  rw [map_zpow, toAdd_zpow,
    divisorMonoidGroupDegree_qParameterGroupification_toAdd]

/-! ## 3. The general-prime finite carrier and its displacement laws -/

noncomputable def primeThetaQHodgeTheater (p : Nat) [Fact (Nat.Prime p)]
    (l : PrimeGeFive) : HodgeTheater l (FinitePrimePlace 2 7) where
  arithmetic := gaussianInitialThetaArithmeticData l
  primeStrip := finiteLocalIntegralFPrimeStrip 2 7
  thetaPacket :=
    FiniteThetaPacket.ofQ (l := l) (primeThetaQ p) (primeThetaQ_pos p)

@[simp] theorem primeThetaQHodgeTheater_q (p : Nat) [Fact (Nat.Prime p)]
    (l : PrimeGeFive) :
    (primeThetaQHodgeTheater p l).thetaPacket.q = primeThetaQ p := rfl

theorem primeThetaQHodgeTheater_log_scale
    (p : Nat) [Fact (Nat.Prime p)] (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    Real.log ((primeThetaQHodgeTheater p l).thetaPacket.scale j) =
      (gaussExponent j.1).toNat * Real.log (primeThetaQ p) := by
  rw [(primeThetaQHodgeTheater p l).thetaPacket.log_scale j,
    primeThetaQHodgeTheater_q]

/-- The Gaussian displacement log-form written through the divisor-monoid
degree, for every prime. -/
theorem primeThetaQHodgeTheater_log_scale_divisor_degree
    (p : Nat) [Fact (Nat.Prime p)] (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    Real.log ((primeThetaQHodgeTheater p l).thetaPacket.scale j) =
      (gaussExponent j.1).toNat *
        Multiplicative.toAdd
          (localIntegralNormDegreeFor p (LocalIntegralMonoid.qParameter p)) := by
  rw [primeThetaQHodgeTheater_log_scale, primeThetaQ_log_eq_local_degree,
    ← qParameter_localIntegralNormDegree_apply]

noncomputable def primeThetaQThreeTheaterSystem (p : Nat) [Fact (Nat.Prime p)]
    (l : PrimeGeFive) : ThreeTheaterSystem l (FinitePrimePlace 2 7) where
  source := primeThetaQHodgeTheater p l
  middle := primeThetaQHodgeTheater p l
  target := primeThetaQHodgeTheater p l
  source_to_middle := HodgeTheaterLink.refl _
  middle_to_target := HodgeTheaterLink.refl _

theorem primeThetaQThreeTheaterSystem_source_log_scale_divisor_degree
    (p : Nat) [Fact (Nat.Prime p)] (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    Real.log ((primeThetaQThreeTheaterSystem p l).source.thetaPacket.scale j) =
      (gaussExponent j.1).toNat *
        Multiplicative.toAdd
          (localIntegralNormDegreeFor p (LocalIntegralMonoid.qParameter p)) := by
  change Real.log ((primeThetaQHodgeTheater p l).thetaPacket.scale j) = _
  exact primeThetaQHodgeTheater_log_scale_divisor_degree p l j

/-! ## 4. The prime family on the integral F-prime-strip -/

noncomputable def finitePlaceQParameter (lower upper : Nat)
    (v : FinitePrimePlace lower upper) :
    (finiteLocalIntegralFPrimeStrip lower upper).Mon v :=
  letI := Fact.mk v.prime
  LocalIntegralMonoid.qParameter v.1

theorem finitePlaceQParameter_degree_toAdd (lower upper : Nat)
    (v : FinitePrimePlace lower upper) :
    Multiplicative.toAdd
      ((finiteLocalIntegralFPrimeStrip lower upper).degree v
        (finitePlaceQParameter lower upper v)) =
      - Real.log (v.1 : ℝ) := by
  letI := Fact.mk v.prime
  change Multiplicative.toAdd
    (localIntegralNormDegreeFor v.1 (LocalIntegralMonoid.qParameter v.1)) =
    - Real.log (v.1 : ℝ)
  exact qParameter_localIntegralNormDegree_toAdd v.1

theorem finitePlaceQParameter_degree_ne_one (lower upper : Nat)
    (v : FinitePrimePlace lower upper) :
    (finiteLocalIntegralFPrimeStrip lower upper).degree v
      (finitePlaceQParameter lower upper v) ≠ 1 := by
  letI := Fact.mk v.prime
  change localIntegralNormDegreeFor v.1 (LocalIntegralMonoid.qParameter v.1) ≠ 1
  exact qParameter_localIntegralNormDegree_ne_one v.1

/-- Every strip equivalence preserves the per-place q-parameter degree. -/
theorem finitePlaceQParameter_degree_preserved (lower upper : Nat)
    (φ : FPrimeStripEquiv (finiteLocalIntegralFPrimeStrip lower upper)
      (finiteLocalIntegralFPrimeStrip lower upper))
    (v : FinitePrimePlace lower upper) :
    (finiteLocalIntegralFPrimeStrip lower upper).degree v
        (φ.isoMon v (finitePlaceQParameter lower upper v)) =
      (finiteLocalIntegralFPrimeStrip lower upper).degree v
        (finitePlaceQParameter lower upper v) :=
  φ.compatDegree v (finitePlaceQParameter lower upper v)

theorem finitePlaceQParameter_degree_preserved_toAdd (lower upper : Nat)
    (φ : FPrimeStripEquiv (finiteLocalIntegralFPrimeStrip lower upper)
      (finiteLocalIntegralFPrimeStrip lower upper))
    (v : FinitePrimePlace lower upper) :
    Multiplicative.toAdd
      ((finiteLocalIntegralFPrimeStrip lower upper).degree v
        (φ.isoMon v (finitePlaceQParameter lower upper v))) =
      - Real.log (v.1 : ℝ) := by
  rw [finitePlaceQParameter_degree_preserved,
    finitePlaceQParameter_degree_toAdd]

/-! ## 5. Reuse of the packaged model Frobenioid at the concrete place -/

namespace ConcreteSourceFrobenioidBridge

/-- The divisor-monoid portion of the packaged model Frobenioid at the
concrete Gaussian place has Grothendieck groupification canonically Z
(reuse of the built finite-stage reconstruction). -/
noncomputable def stageDivisorGroupificationEquivInt
    (stage : concreteStageBase) :
    Algebra.GrothendieckAddGroup
      ((concreteStageModelDivisorialMonoid).obj stage).carrier ≃+ ℤ :=
  Iut.SourceFinitePlaceReconstruction.stageDivisorGrothendieckEquivInt

/-- The divisor-monoid field of the packaged model Frobenioid is the concrete
stage divisorial monoid reused above. -/
theorem stageModelPreFrobenioid_divisorMonoid_eq :
    concreteStageModel.preFrobenioid.divisorMonoid =
      concreteStageModelDivisorialMonoid := rfl

end ConcreteSourceFrobenioidBridge

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def thetaLinkFrobenioidDivisorMonoidReduction : Obligation :=
  { id := "IUT-I.theta-link-frobenioid-divisor-monoid-reduction"
    source :=
      "IUT I: Remark 3.8.1 (i) (the Theta-link maps n Theta_v |-> (n+1) " ++
        "q_v) and (ii) (the divisor monoid portion [i.e., q_v and Theta_v] " ++
        "of the various Frobenioids that appear in a Theta-Hodge theater)"
    status := VerificationStatus.interface
    note :=
      "General-prime reduction of the displacement arithmetic at the " ++
        "divisor-monoid portion: for every rational prime p, the " ++
        "q-parameter of the nonzero integral-closure monoid and of its " ++
        "Grothendieck groupification has norm-log degree -log p, nontrivial " ++
        "for every prime; the finite-model carrier with q-value " ++
        "primeThetaQ p satisfies the Gaussian displacement laws with the " ++
        "log-form written through the divisor-monoid degree; on the " ++
        "integral F-prime-strip the per-place degree law holds for every " ++
        "finite place and is preserved by strip equivalences. The packaged " ++
        "model Frobenioid divisor monoid (groupification Z) is reused at " ++
        "the concrete Gaussian place, but the bridge from it to the local " ++
        "p-adic q-parameter is not constructed: card C2b-general. The " ++
        "scheme theory between q_v and Theta_v stays parked."
    dependsOn :=
      [ "IUT-I.theta-link-arithmetic-displacement-reduction",
        "IUT-II.concrete-local-q-parameter-roots",
        "IUT-II.local-integral-monoid-carrier",
        "IUT-II.local-integral-f-prime-strip-carrier",
        "IUT-I-II.concrete-source-frobenioid-bridge" ] }

end LeanFormal.IUT.Audit
