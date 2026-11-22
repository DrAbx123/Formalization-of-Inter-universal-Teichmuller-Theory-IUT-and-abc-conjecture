/-
  # Theta generator and distinct-history feasibility for the Example 3.6 carrier

  Task task-53 of the Group-1 split; it attacks residual gap (2) of the
  Example36 source-theater carrier: actual theta generators and distinct initial
  Theta histories.

  ## What the tree provides (constructed here)

  * The actual finite theta packet of the concrete Example 3.6 carrier: its
    q-value is the actual local q-parameter norm gaussianFiveThetaQ = 1/5, its
    scales are the actual Gaussian special values, and it carries the actual
    finite reduction/generator data of the C-stage.  This finite packet data is
    assembled in Example36ThetaGeneratorData (packet, finite reduction, finite
    generator, compatible roots) with the defining equalities to the existing
    carriers, and its order/kernel/positivity properties are proved.
  * A second, genuinely distinct, Hodge theater with the SAME theta packet and
    the SAME prime strip as the concrete source theater: the Gaussian finite
    integral theater concreteInitialThetaHodgeTheater.  It differs from the
    source theater in its arithmetic curve (the base-changed split curve versus
    the Gaussian curve y^2 + y = x^3), proved by separating the a_6 coefficient
    (5 versus 0).  A HodgeTheaterLink between the two theaters is constructed;
    its prime-strip equivalence is the identity, and a non-reflexive two-step
    dependent history with distinct source and terminal theater is built.

  ## What the tree does NOT provide (frozen cards)

  * No actual etale theta generator, theta series, or theta q-expansion is
    available in the tree: the whole theta data is the finite packet of Gaussian
    special values.  Searched modules contain no q-expansion/theta-series API.
    Frozen as SourceThetaGeneratorCard.
  * No genuinely distinct initial Theta history with a nontrivial (anabelian)
    Theta-link exists in the tree: the link API HodgeTheaterLink forces equality
    of the q-value and of every theta scale, and the link constructed here has
    identity prime-strip equivalence.  A second theater with a different theta
    generator cannot be linked at all (this is the precise obstruction, proved
    below).  Frozen as SourceDistinctThetaHistoryCard.

  No fake history, no constant/identity substitution for source data, and no
  theta-pilot/q-pilot claim is made anywhere in this file.  The second theater
  and its identity-prime-strip link are recorded as finite carrier tests, not as
  the source's distinct anabelian history.

  Source correspondence: IUT I, Definition 3.6 (Theta-Hodge theaters),
  Corollary 3.7 (i) and Remark 3.7.1 (Theta-links), Corollary 3.8 and
  Remark 3.8.1 (i) (the Z-chain and the Theta-link n Theta_v |-> (n+1) q_v);
  IUT II, theta evaluation and q-expansion.
-/

import LeanFormal.IUT.IUTII.Theta.ConcreteSourceHistoryLinkBridge
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceTheaterCarrier
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteInitialThetaTransport
import LeanFormal.IUT.IUTI.HodgeTheater.SourceHodgeTheaterFamilyLawsReduction
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36
namespace ThetaGeneratorFeasibility

open LeanFormal.IUT
open LeanFormal.IUT.ConcreteSourceEtaleThetaBridge
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier
open IsDedekindDomain

local instance gaussianPolynomialIrreducibleFactThetaGenerator :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance fivePrimeFactThetaGenerator : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

local instance primeFactThetaGenerator (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

noncomputable section

/-! ## 1. The actual finite theta generator data of the Example 3.6 carrier -/

/-- The finite theta generator data actually available in the tree for the
concrete Example 3.6 carrier: the finite theta packet of the source theater, the
finite reduction of the C-stage Kummer packet, its canonical finite generator,
and the compatible root system.  Every field is held equal to the existing
carrier data by a definitional equality; nothing here is a new geometric
existence claim. -/
structure Example36ThetaGeneratorData (l : PrimeGeFive) where
  thetaPacket : FiniteThetaPacket l
  thetaPacket_eq : thetaPacket = (sourceTheater l).thetaPacket
  reduction : ℤ →+ ZMod l.value
  reduction_eq : reduction =
    (ConcreteSourceEtaleThetaBridge.packet l).finiteReduction
  finiteGenerator : ZMod l.value
  finiteGenerator_eq : finiteGenerator = reduction 1
  compatibleRoots : CompatibleRootSystem
    (Algebra.GrothendieckGroup (LocalIntegralMonoid l.value))
    (LocalIntegralMonoid.qParameterGroupification l.value)
  compatibleRoots_eq : compatibleRoots =
    (ConcreteSourceEtaleThetaBridge.packet l).compatibleRoots

noncomputable def example36ThetaGeneratorData (l : PrimeGeFive) :
    Example36ThetaGeneratorData l where
  thetaPacket := (sourceTheater l).thetaPacket
  thetaPacket_eq := rfl
  reduction := (ConcreteSourceEtaleThetaBridge.packet l).finiteReduction
  reduction_eq := rfl
  finiteGenerator := generator l
  finiteGenerator_eq := generator_eq_reduction_one l
  compatibleRoots := (ConcreteSourceEtaleThetaBridge.packet l).compatibleRoots
  compatibleRoots_eq := rfl

@[simp] theorem example36ThetaGeneratorData_thetaPacket (l : PrimeGeFive) :
    (example36ThetaGeneratorData l).thetaPacket = (sourceTheater l).thetaPacket :=
  rfl

@[simp] theorem example36ThetaGeneratorData_reduction (l : PrimeGeFive) :
    (example36ThetaGeneratorData l).reduction =
      (ConcreteSourceEtaleThetaBridge.packet l).finiteReduction :=
  rfl

@[simp] theorem example36ThetaGeneratorData_finiteGenerator (l : PrimeGeFive) :
    (example36ThetaGeneratorData l).finiteGenerator = generator l :=
  rfl

@[simp] theorem example36ThetaGeneratorData_compatibleRoots (l : PrimeGeFive) :
    (example36ThetaGeneratorData l).compatibleRoots =
      (ConcreteSourceEtaleThetaBridge.packet l).compatibleRoots :=
  rfl

theorem example36ThetaGeneratorData_q (l : PrimeGeFive) :
    (example36ThetaGeneratorData l).thetaPacket.q = gaussianFiveThetaQ := by
  rw [example36ThetaGeneratorData_thetaPacket, sourceTheater_theta_q]

theorem example36ThetaGeneratorData_q_eq_inv_five (l : PrimeGeFive) :
    (example36ThetaGeneratorData l).thetaPacket.q = (5 : ℝ)⁻¹ := by
  rw [example36ThetaGeneratorData_q, gaussianFiveThetaQ_eq_inv_five]

theorem example36ThetaGeneratorData_scale (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    (example36ThetaGeneratorData l).thetaPacket.scale j =
      realThetaValue gaussianFiveThetaQ j.1 := by
  rw [example36ThetaGeneratorData_thetaPacket, sourceTheater_theta_scale]

theorem example36ThetaGeneratorData_reduction_kernel (l : PrimeGeFive) :
    (example36ThetaGeneratorData l).reduction.ker =
      AddSubgroup.zmultiples (l.value : ℤ) := by
  rw [example36ThetaGeneratorData_reduction]
  exact (ConcreteSourceEtaleThetaBridge.packet l).finiteReduction_kernel

theorem example36ThetaGeneratorData_reduction_surjective (l : PrimeGeFive) :
    Function.Surjective (example36ThetaGeneratorData l).reduction := by
  rw [example36ThetaGeneratorData_reduction]
  exact (ConcreteSourceEtaleThetaBridge.packet l).finiteReduction_surjective

theorem example36ThetaGeneratorData_finiteGenerator_order (l : PrimeGeFive) :
    addOrderOf (example36ThetaGeneratorData l).finiteGenerator = l.value := by
  rw [example36ThetaGeneratorData_finiteGenerator]
  exact generator_order l

theorem example36ThetaGeneratorData_finiteGenerator_ne_zero
    (l : PrimeGeFive) :
    (example36ThetaGeneratorData l).finiteGenerator ≠ 0 := by
  rw [example36ThetaGeneratorData_finiteGenerator]
  exact generator_ne_zero l

theorem example36ThetaGeneratorData_finiteGenerator_eq_reduction_one
    (l : PrimeGeFive) :
    (example36ThetaGeneratorData l).finiteGenerator =
      (example36ThetaGeneratorData l).reduction 1 := by
  rw [example36ThetaGeneratorData_finiteGenerator]
  exact generator_eq_reduction_one l

end

noncomputable section

/-! ## 2. A second distinct theater with the same theta packet -/

/-- A second concrete Hodge theater: the Gaussian finite integral theater of the
existing C-stage transport.  It has the same prime strip and the same theta
packet as the source theater, and a different arithmetic curve. -/
noncomputable def secondThetaTheater (l : PrimeGeFive) :
    HodgeTheater l (FinitePrimePlace 2 7) :=
  concreteInitialThetaHodgeTheater l

@[simp] theorem secondThetaTheater_arithmetic (l : PrimeGeFive) :
    (secondThetaTheater l).arithmetic = gaussianInitialThetaArithmeticData l :=
  rfl

@[simp] theorem secondThetaTheater_primeStrip (l : PrimeGeFive) :
    (secondThetaTheater l).primeStrip = finiteLocalIntegralFPrimeStrip 2 7 :=
  rfl

@[simp] theorem secondThetaTheater_thetaPacket (l : PrimeGeFive) :
    (secondThetaTheater l).thetaPacket =
      FiniteThetaPacket.ofQ gaussianFiveThetaQ gaussianFiveThetaQ_pos :=
  rfl

theorem secondThetaTheater_q (l : PrimeGeFive) :
    (secondThetaTheater l).thetaPacket.q = gaussianFiveThetaQ := by
  rw [secondThetaTheater_thetaPacket]
  rfl

/-- The Gaussian model y^2 + y = x^3 has a_6 = 0. -/
theorem gaussianPuncturedCurve_a6 :
    gaussianPuncturedCurve.curve.a₆ = (0 : GaussianField) := by
  rw [gaussianPuncturedCurve_curve,
    WeierstrassCurve.ofJ_0_of_three_ne_zero (by norm_num : (3 : GaussianField) ≠ 0)]
  rfl

/-- The base-changed split multiplicative curve has a_6 = 5. -/
theorem concreteSplitPuncturedCurve_baseChange_a6 :
    (concreteSplitPuncturedCurve.baseChange GaussianField).curve.a₆ =
      (5 : GaussianField) := by
  rw [show (concreteSplitPuncturedCurve.baseChange GaussianField).curve =
    concreteSplitCurve.baseChange GaussianField from rfl]
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₆, concreteSplitCurve]
  norm_num

/-- The concrete Gaussian initial Theta arithmetic data (base-changed split
curve) differs from the Gaussian initial Theta arithmetic data (the curve
y^2 + y = x^3), separated by the a_6 coefficient. -/
theorem concreteGaussianInitialThetaArithmeticData_ne_gaussian
    (l : PrimeGeFive) :
    concreteGaussianInitialThetaArithmeticData l ≠
      gaussianInitialThetaArithmeticData l := by
  intro h
  have hhe : HEq (concreteGaussianInitialThetaArithmeticData l).curve
      (gaussianInitialThetaArithmeticData l).curve :=
    @Eq.rec (InitialThetaArithmeticData l) (gaussianInitialThetaArithmeticData l)
      (fun X _ => HEq X.curve (gaussianInitialThetaArithmeticData l).curve)
      (HEq.refl (gaussianInitialThetaArithmeticData l).curve)
      (concreteGaussianInitialThetaArithmeticData l) h.symm
  have hc : (concreteGaussianInitialThetaArithmeticData l).curve =
      (gaussianInitialThetaArithmeticData l).curve := eq_of_heq hhe
  rw [concreteGaussianInitialThetaArithmeticData_curve,
    gaussianInitialThetaArithmeticData_curve] at hc
  have h6 := congrArg
    (fun c : PuncturedEllipticCurve GaussianField => c.curve.a₆) hc
  rw [concreteSplitPuncturedCurve_baseChange_a6,
    gaussianPuncturedCurve_a6] at h6
  norm_num at h6

/-- The source theater and the second theater have different arithmetic data. -/
theorem sourceTheater_arithmetic_ne_secondThetaTheater_arithmetic
    (l : PrimeGeFive) :
    (sourceTheater l).arithmetic ≠ (secondThetaTheater l).arithmetic := by
  rw [sourceTheater_arithmetic, secondThetaTheater_arithmetic]
  exact concreteGaussianInitialThetaArithmeticData_ne_gaussian l

/-- The second theater is genuinely distinct from the source theater. -/
theorem sourceTheater_ne_secondThetaTheater (l : PrimeGeFive) :
    sourceTheater l ≠ secondThetaTheater l := by
  intro h
  exact sourceTheater_arithmetic_ne_secondThetaTheater_arithmetic l
    (congrArg HodgeTheater.arithmetic h)

/-- A link from the source theater to the second theater.  Its prime-strip
equivalence is the identity: it carries no anabelian prime-strip information.
This is a finite carrier test link, not the source's Theta-link. -/
noncomputable def secondThetaTheaterLink (l : PrimeGeFive) :
    HodgeTheaterLink (sourceTheater l) (secondThetaTheater l) where
  primeStripEquiv := FPrimeStripEquiv.refl _
  theta_q_eq := rfl
  theta_scale_eq := by
    intro j
    rfl

theorem secondThetaTheaterLink_primeStripEquiv (l : PrimeGeFive) :
    (secondThetaTheaterLink l).primeStripEquiv =
      FPrimeStripEquiv.refl ((sourceTheater l).primeStrip) :=
  rfl

/-- The link's prime-strip equivalence is the identity on every local Pi. -/
theorem secondThetaTheaterLink_isoPi (l : PrimeGeFive)
    (v : FinitePrimePlace 2 7) :
    (secondThetaTheaterLink l).primeStripEquiv.isoPi v =
      MulEquiv.refl ((sourceTheater l).primeStrip.toDPrimeStrip.Pi v) :=
  rfl

/-- The link's prime-strip equivalence is the identity on every local Mon. -/
theorem secondThetaTheaterLink_isoMon (l : PrimeGeFive)
    (v : FinitePrimePlace 2 7) :
    (secondThetaTheaterLink l).primeStripEquiv.isoMon v =
      MulEquiv.refl ((sourceTheater l).primeStrip.Mon v) :=
  rfl

/-- A non-reflexive two-step dependent history whose source is the concrete
source theater and whose terminal is the distinct second theater. -/
noncomputable def secondThetaTheaterHistory (l : PrimeGeFive) :
    HodgeTheaterHistory l (FinitePrimePlace 2 7) (sourceTheater l) :=
  .cons (secondThetaTheaterLink l) (.singleton (secondThetaTheater l))

theorem secondThetaTheaterHistory_terminal (l : PrimeGeFive) :
    (secondThetaTheaterHistory l).terminal = secondThetaTheater l :=
  rfl

theorem secondThetaTheaterHistory_length (l : PrimeGeFive) :
    (secondThetaTheaterHistory l).length = 2 :=
  rfl

theorem secondThetaTheaterHistory_composite (l : PrimeGeFive) :
    (secondThetaTheaterHistory l).composite = secondThetaTheaterLink l :=
  HodgeTheaterLink.trans_refl (secondThetaTheaterLink l)

theorem secondThetaTheaterHistory_source_ne_terminal (l : PrimeGeFive) :
    sourceTheater l ≠ (secondThetaTheaterHistory l).terminal := by
  rw [secondThetaTheaterHistory_terminal]
  exact sourceTheater_ne_secondThetaTheater l

theorem secondThetaTheaterHistory_ne_singleton (l : PrimeGeFive) :
    secondThetaTheaterHistory l ≠
      HodgeTheaterHistory.singleton (sourceTheater l) := by
  intro h
  have hlen := congrArg HodgeTheaterHistory.length h
  simp only [secondThetaTheaterHistory_length,
    HodgeTheaterHistory.length_singleton] at hlen
  omega

/-! ## 3. Theta transport obstruction for any link -/

/-- Any HodgeTheaterLink from the source theater forces the target q-value to be
the source q-value gaussianFiveThetaQ. -/
theorem link_target_theta_q {l : PrimeGeFive}
    {T : HodgeTheater l (FinitePrimePlace 2 7)}
    (link : HodgeTheaterLink (sourceTheater l) T) :
    T.thetaPacket.q = gaussianFiveThetaQ :=
  (link.theta_q_eq.symm).trans (sourceTheater_theta_q l)

/-- Any HodgeTheaterLink from the source theater forces every target theta scale
to be the source theta scale. -/
theorem link_target_theta_scale {l : PrimeGeFive}
    {T : HodgeTheater l (FinitePrimePlace 2 7)}
    (link : HodgeTheaterLink (sourceTheater l) T)
    (j : SignedLabel l.value) :
    T.thetaPacket.scale j = (sourceTheater l).thetaPacket.scale j :=
  (link.theta_scale_eq j).symm

/-- Any HodgeTheaterLink from the source theater forces every target theta scale
to be the actual Gaussian special value of gaussianFiveThetaQ. -/
theorem link_target_theta_scale_gaussian {l : PrimeGeFive}
    {T : HodgeTheater l (FinitePrimePlace 2 7)}
    (link : HodgeTheaterLink (sourceTheater l) T)
    (j : SignedLabel l.value) :
    T.thetaPacket.scale j = realThetaValue gaussianFiveThetaQ j.1 :=
  (link_target_theta_scale link j).trans (sourceTheater_theta_scale l j)

/-- **Precise theta-transport obstruction.**  A theater whose theta q-value
differs from gaussianFiveThetaQ admits no HodgeTheaterLink from the source
theater. -/
theorem no_link_to_different_theta_q {l : PrimeGeFive}
    {T : HodgeTheater l (FinitePrimePlace 2 7)}
    (h : T.thetaPacket.q ≠ gaussianFiveThetaQ) :
    ¬ Nonempty (HodgeTheaterLink (sourceTheater l) T) := by
  rintro ⟨link⟩
  exact h (link_target_theta_q link)

/-- A theater whose theta scales differ from the source scales admits no
HodgeTheaterLink from the source theater. -/
theorem no_link_to_different_theta_scale {l : PrimeGeFive}
    {T : HodgeTheater l (FinitePrimePlace 2 7)}
    (j : SignedLabel l.value)
    (h : T.thetaPacket.scale j ≠ (sourceTheater l).thetaPacket.scale j) :
    ¬ Nonempty (HodgeTheaterLink (sourceTheater l) T) := by
  rintro ⟨link⟩
  exact h (link_target_theta_scale link j)

/-- The constructed second-theater link has the same q and all the same theta
scales as the source theater: the second theater is genuinely linkable only
because its theta generator data is identical. -/
theorem secondThetaTheater_link_theta_data (l : PrimeGeFive) :
    (secondThetaTheater l).thetaPacket.q = gaussianFiveThetaQ ∧
    (∀ j : SignedLabel l.value,
      (secondThetaTheater l).thetaPacket.scale j =
        (sourceTheater l).thetaPacket.scale j) :=
  ⟨link_target_theta_q (secondThetaTheaterLink l),
    fun j => link_target_theta_scale (secondThetaTheaterLink l) j⟩

/-! ## 4. Frozen cards for the missing source theta data -/

/-- **Frozen card for the missing actual source theta generator.**  The tree has
only the finite packet of Gaussian special values; it has no actual etale theta
function or theta series over the source curve and no theta q-expansion.  The
card records the shape of that missing data: a theta carrier together with its
q-expansion, a q-value constrained to the actual gaussianFiveThetaQ, and theta
special values at the signed finite labels.  No inhabitant is constructed in
this file and no theorem consumes one; the finite packet above is not
substituted for this card. -/
structure SourceThetaGeneratorCard (l : PrimeGeFive) where
  /-- The actual source theta function / theta series carrier. -/
  Theta : Type
  /-- Its q-expansion coefficients. -/
  qExpansion : Theta → ℤ → ℝ
  /-- The q-value of the source theta generator. -/
  q : ℝ
  /-- The source q-value must be the actual tree q-value gaussianFiveThetaQ. -/
  q_eq_gaussian : q = gaussianFiveThetaQ
  /-- Theta special values at the signed finite labels. -/
  specialValue : SignedLabel l.value → ℝ

/-- **Frozen card for the missing distinct initial Theta history.**  The source
requires a nonconstant family of Hodge theaters together with a nontrivial
Theta-link (n Theta_v |-> (n+1) q_v) transporting theta generators between
distinct histories.  The tree has only HodgeTheaterLink, which forces equality
of theta q-values and scales and, in the constructed finite witness, identity
prime-strip equivalence.  The card records the shape of the missing data: an
index with two distinct members, an injective family of theaters, links between
all pairs, and a nontrivial theta transport on the frozen generator card.  No
inhabitant is constructed and the finite second-theater history above is not
substituted for this card. -/
structure SourceDistinctThetaHistoryCard (l : PrimeGeFive) where
  /-- The frozen actual source theta generator. -/
  generator : SourceThetaGeneratorCard l
  /-- The index of the source's history family (the Z-chain in the paper). -/
  index : Type
  /-- The index has at least two distinct elements. -/
  twoDistinct : ∃ i j : index, i ≠ j
  /-- The era-dependent Hodge theaters. -/
  theater : index → HodgeTheater l (FinitePrimePlace 2 7)
  /-- The theaters are pairwise distinct. -/
  theater_injective : Function.Injective theater
  /-- Theta-links between every pair of theaters. -/
  link : ∀ i j, HodgeTheaterLink (theater i) (theater j)
  /-- The Theta-link transport on the source theta generator. -/
  thetaTransport : generator.Theta → generator.Theta
  /-- The Theta-link transport is genuinely nontrivial. -/
  thetaTransport_nontrivial : ∃ t : generator.Theta, thetaTransport t ≠ t

/-! ## 5. Which task-20 gaps are actual and which are cards -/

/-- The residual gaps of the Example36 source-theater carrier recorded in
task-20. -/
inductive Example36ResidualGap
  | placeIndexedPrimeStrip
  | sourceThetaGeneratorAndDistinctHistories
  | stageNormalizationBridge
  | thetaPilotAndSourceIdentifications
  deriving DecidableEq, Repr

/-- Status of a residual gap: actually proved, partially actual (some layers
proved, the source identification frozen as a card), or entirely frozen as a
card. -/
inductive Example36ResidualGapStatus
  | actual
  | partiallyActual
  | frozenCard
  deriving DecidableEq, Repr

/-- Status assignment for the task-20 residual gaps as of this file:
* the stage-model normalization bridge is actually proved (task-30,
  Example36StageNormalizationBridge);
* the place-indexed prime strip is partially actual: the value/degree layer and
  the arithmetic Galois side are constructed (task-40/45/47), while the
  D-prime-strip mono-analytic/curve-Pi data remains a card;
* the source theta generator and distinct initial Theta histories are frozen
  cards (this file's SourceThetaGeneratorCard and
  SourceDistinctThetaHistoryCard);
* the theta-pilot/q-pilot and further source identifications remain frozen cards
  and are not claimed. -/
def example36ResidualGapStatus :
    Example36ResidualGap → Example36ResidualGapStatus
  | .placeIndexedPrimeStrip => .partiallyActual
  | .sourceThetaGeneratorAndDistinctHistories => .frozenCard
  | .stageNormalizationBridge => .actual
  | .thetaPilotAndSourceIdentifications => .frozenCard

/-! ## 6. Summary -/

/-- **Summary of theta generator/distinct-history feasibility.**  The actual
finite theta packet/generator data of the Example 3.6 carrier is assembled and
its q = 1/5, generator order, exact kernel and Gaussian special values are
proved; a genuinely distinct second theater with the same theta packet and
prime strip exists and is linked by an identity-prime-strip link, so a
non-reflexive two-step history with distinct endpoints exists; and any link from
the source theater is forced to preserve the q-value and every theta scale, so a
second theater with a different theta generator cannot be linked.  The actual
source theta generator/q-expansion and the nontrivial distinct Theta history are
frozen as cards. -/
theorem example36ThetaGeneratorFeasibility_summary :
    (∀ l : PrimeGeFive,
      (example36ThetaGeneratorData l).thetaPacket.q = gaussianFiveThetaQ) ∧
    (∀ l : PrimeGeFive,
      addOrderOf (example36ThetaGeneratorData l).finiteGenerator = l.value) ∧
    (∀ l : PrimeGeFive, sourceTheater l ≠ secondThetaTheater l) ∧
    (∀ l : PrimeGeFive,
      (secondThetaTheaterLink l).primeStripEquiv =
        FPrimeStripEquiv.refl ((sourceTheater l).primeStrip)) ∧
    (∀ (l : PrimeGeFive) (T : HodgeTheater l (FinitePrimePlace 2 7)),
      HodgeTheaterLink (sourceTheater l) T → T.thetaPacket.q = gaussianFiveThetaQ) :=
  ⟨fun _ => example36ThetaGeneratorData_q _,
    fun _ => example36ThetaGeneratorData_finiteGenerator_order _,
    fun _ => sourceTheater_ne_secondThetaTheater _,
    fun _ => secondThetaTheaterLink_primeStripEquiv _,
    fun _ _ link => link_target_theta_q link⟩

end

end ThetaGeneratorFeasibility
end Example36
end Frobenioid
end IUTII
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for theta generator/distinct-history feasibility.  The actual
finite theta packet/generator data of the concrete Example 3.6 carrier is
assembled (q = gaussianFiveThetaQ = 1/5, finite reduction with exact kernel,
canonical finite generator of order l, compatible roots); a genuinely distinct
second theater with the same theta packet and prime strip is constructed and
linked by an identity-prime-strip link, giving a non-reflexive two-step history
with distinct endpoints; any link from the source theater is proved to preserve
q and every theta scale, so a theater with a different theta generator cannot be
linked; the actual source theta generator/q-expansion and the nontrivial
distinct Theta history are frozen as cards.  Task-20 gaps: stage normalization is
actual, the place-indexed strip is partially actual, the source theta
generator/distinct histories and theta-pilot/source identifications are cards.
No fake history or constant/identity substitution is made and no
theta-pilot/q-pilot/Tate claim is added. -/
def example36ThetaGeneratorFeasibility : Obligation :=
  { id := "IUT-II.example36-theta-generator-feasibility"
    source :=
      "IUT I, Definition 3.6; Corollary 3.7 (i) and Remark 3.7.1; " ++
        "Corollary 3.8 and Remark 3.8.1 (i); IUT II, theta evaluation and " ++
        "q-expansion"
    status := VerificationStatus.interface
    note :=
      "Constructed the actual finite theta generator data of the Example 3.6 " ++
        "carrier: theta packet with q = gaussianFiveThetaQ = 1/5, actual finite " ++
        "reduction with kernel l*Z, canonical finite generator of order l, " ++
        "compatible roots, and Gaussian special values " ++
        "(Example36ThetaGeneratorData, example36ThetaGeneratorData_q, " ++
        "_finiteGenerator_order, _reduction_kernel, _scale).  Constructed a " ++
        "genuinely distinct second theater with the same prime strip and theta " ++
        "packet (concreteInitialThetaHodgeTheater), proved distinct by the a_6 " ++
        "coefficient (5 versus 0), linked to the source theater with an " ++
        "identity prime-strip equivalence, and assembled into a non-reflexive " ++
        "two-step dependent history with distinct source and terminal " ++
        "(secondThetaTheater, sourceTheater_ne_secondThetaTheater, " ++
        "secondThetaTheaterLink, secondThetaTheaterHistory).  Proved the precise " ++
        "obstruction: any HodgeTheaterLink from the source theater forces the " ++
        "target q-value and every target theta scale to agree with the source " ++
        "(link_target_theta_q, link_target_theta_scale, " ++
        "no_link_to_different_theta_q, no_link_to_different_theta_scale); thus no " ++
        "second theater with a different theta generator can be linked.  No " ++
        "actual etale theta generator/theta series/q-expansion exists in the " ++
        "tree (frozen as SourceThetaGeneratorCard) and no nontrivial distinct " ++
        "Theta history/Theta-link exists (frozen as SourceDistinctThetaHistoryCard); " ++
        "the finite identity-prime-strip link and finite second theater are " ++
        "recorded, not substituted.  Task-20 residual gap status: stage " ++
        "normalization actual; place-indexed strip partially actual; source theta " ++
        "generator/distinct histories and theta-pilot/source identifications " ++
        "cards (example36ResidualGapStatus).  No theta-pilot/q-pilot/Tate claim."
    dependsOn :=
      [ "IUT-II.example36-source-theater-carrier",
        "IUT-II.example36-stage-normalization-bridge",
        "IUT-II.example36-gaussian-place-strip",
        "IUT-I.hodge-theater-family-laws-reduction",
        "IUT-I-II.concrete-source-algebraic-theta-bridge",
        "IUT-I.hodge-theater-history-composition" ] }

end LeanFormal.IUT.Audit
