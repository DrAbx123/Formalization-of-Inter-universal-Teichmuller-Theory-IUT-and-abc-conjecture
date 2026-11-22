import LeanFormal.IUT.IUTII.Frobenioid.PrimeStripFrobenioidCards
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Data.Set.Countable

/-!
# CAT-R / MOD-R skeleton rounds for the prime strips -> Frobenioid link layer

This module is the CAT-R / MOD-R attack round on top of
`PrimeStripFrobenioidCards.lean` (SHA 43BA0BB2...FD1435) for the obligation
`IUT-I-II.prime-strips-frobenioids` (`IUTII/Frobenioid/PrimeStrips.lean:5`).

## CAT-R (the minimal skeleton for `Cv`, `C⊢v`, `C⊩mod`)

Source: IUT I, Example 3.3, (i) (txt line 4132ff): `Cv`, `C⊢v` are the
`pv`-adic Frobenioids whose base categories are `Dv`, `D⊢v`; IUT I,
Example 3.5, (i) (txt line 4569ff): `C⊩mod` is a realified Frobenioid; and
IUT I, Definition 5.2, (i)-(iv) (txt lines 7702-7775): the F/F⊢/F⊩-prime-strips
are built from these categories.

Frozen conclusions (with the Lean statements below):

* The weakest consumer-facing skeleton in the tree is the contract
  `PrimeStripFrobenioidLinkLayer` over two `FrobenioidValueKernel`s; the
  theorem `primeStripFrobenioidLinkLayer_exists_iff_cards` shows it is
  *exactly* the pair of directional cards `ModDirectionCard`,
  `MODDirectionCard` at fixed kernels: no layer without both cards, and the
  two cards assemble a layer.
* The weakest categorical start in the tree is the existing
  `Iut.DivisorialAddMonoid` / `Iut.DivisorialMonoidOn` / `Iut.PreFrobenioid` /
  `Iut.PreFrobenioidPresentation` layer (Frobenioids I, section 0 and
  Definition 1.1, (i); txt lines 464-465, 810-815); no new structure is
  needed at this level.
* Precise obstacles (missing types):
  (a) a sharp divisorial monoid of effective geometric divisors (the pf part
      of `ord(O⊿_L)`, Frobenioids II, Example 1.1) -- impossible for the
      current group-valued carriers (`frobenioidLinkUnitStrip_no_divisorialAddMonoid`,
      `frobenioidLinkIntegralStrip_not_sharp` in `PrimeStripFrobenioidCards`),
      lifted here to every fibre of any `DivisorialMonoidOn` by
      `no_divisorialMonoidOn_fibre_of_addEquiv`;
  (b) the FSM morphism class of `Dv`/`D⊢v` (finite etale coverings), present
      only as the `IsFSM` predicate parameter;
  (c) the structure functor with divisor/Frobenius-degree compatibility
      (the `τ⊢` splitting), no instance on the prime-strip carriers.
* Derived no-go: `no_primeStripFrobenioidLinkLayer_finitePlaceModel` -- the
  finite-place model cannot realize even the reduced consumer skeleton,
  because the MOD direction fails at its degree kernels (the degree-gap
  obstruction of `PrimeStripFrobenioidCards`).  The finite model must not be
  inflated to the general claim.

## MOD-R (norm arithmetic at a nonarchimedean place)

Source: IUT III, Example 3.6, (i)-(iii) (txt line 6181ff): the rational
function torsor representation `F⊛MOD` and the local fractional ideal
representation `F⊛mod` of the global Frobenioids, with the natural
isomorphism `F⊛mod ≅ F⊛MOD`; IUT I, Example 3.5, (i): the restriction
normalization `log⊢mod(pv) ↦ 1/[Kv:(Fmod)v] · logΦ(pv)`.

The norm side frozen here (reduced form at the local field `ℚ̄p`): the norm
image of `(ℚ̄p)^×` should be exactly `p^ℚ = {p^q | q : ℚ}` inside `ℝ`.
`PadicNormImageCard p` is that equation; `padicNormImageCard_iff` splits it
into the arithmetic-surjectivity half `PadicNormImageSurjective p`
(`p^ℚ ⊆` norm image) and the rationality half `PadicNormImageRational p`
(norm image `⊆ p^ℚ`).  Proved in this round:

* `padicAlgClNormImage_surjective`: `p^ℚ ⊆` norm image, by adjoining the
  `b`-th root of `p` in `ℚ̄p` (`IsAlgClosed.exists_pow_nat_eq`) and computing
  its norm `p^(-1/b)` (`norm_pow`, `PadicAlgCl.norm_extends`, `Padic.norm_p`);
* `frobenioidLinkUnitStrip_degreeImage_ratLog`: the degree image of the
  unit-strip carrier at `v` contains all of `ℚ · log p`, upgrading the single
  unit computation `inversePrimeUnit_degree` (= log p) of the cards module;
* `padicPowSet_countable`: `p^ℚ` is countable;
* `not_surjective_padicPow`: `q ↦ p^q` cannot be surjective onto `ℝ`
  (counting: countable range versus uncountable `ℝ`);
* `exists_padicPow_between`, `padicAlgClNormImage_dense_positives`: `p^ℚ`
  and the norm image are dense in the positive reals (between-statement).

Parked with recorded cards (see also the audit note and the task report):
(i) the rationality half `PadicNormImageRational p` -- needs the value-group
computation `v((ℚ̄p)^×) = ℚ`, absent from Mathlib `PadicAlgCl`; (ii) the
torsor/fractional-ideal representations `F⊛MOD`, `F⊛mod` and the natural
isomorphism of IUT III, Example 3.6.

## Boundary item specs (one line each)

* (1) etale π1: object = geometric fundamental group with a surjection `proj`
  onto the local absolute Galois group such that `Ker(proj)` is nontrivial,
  quantified over `v ∈ V^non` for every D-prime-strip; consumers =
  `VerticalLogKummer` Frobenioid input and the K1/K2 realization; hard
  because it requires the anabelian reconstruction (`π1(‡Dv) ↦ πrat₁(‡Dv)`,
  Absolute Anabelian Geometry III machinery) absent from the tree -- the
  current `proj` is `MonoidHom.id`.
* (2) `V_K` transport / `ρv` normalization: object = number-field place
  carriers `K_v` of the base field `K = Fmod` together with the transport
  over `V_K`; quantified over all places of `K`; the comparison is
  `ρv : Φ(C⊩mod),v ≅ Φrlf(C⊢v)` with
  `log⊢mod(pv) ↦ 1/[Kv:(Fmod)v] · logΦ(pv)` (IUT I, Example 3.5, (i));
  consumers = `SourceOriginalInput`, K2; hard because the tree has only
  `RationalPrimePlace` carriers (`K = ℚ`), no completion / transport /
  ramification index data.
* (4) arithmetic Frobenius: object = Frobenius dynamics (the power morphisms
  with Frobenius degree) on the value/divisor monoid and its log-shell
  compatibility; quantified over elemental morphisms of the Frobenioid
  structure (Frobenioids I, Definition 1.2/1.3); consumers =
  `VerticalLogKummerCorrespondence.upperSemi`, `Ind3`; hard because there is
  no Frobenioid instance on the carriers (blocked by the CAT-R obstacles
  above; in particular the divisorial layer is not built).

## Consumers

`K2FrobenioidBoundary` / `k2FromFrobenioidCards`
(`IUTIII/Theorem311/SourceK1K2Construction.lean:350-385, 523, 676-679`),
the Theorem 3.11 source chain, and `SourceHodgeTheaterBridge`.
-/

open CategoryTheory

noncomputable section

namespace LeanFormal.IUT

universe u ux uy

/-! ## 1. CAT-R: the weakest in-tree skeleton and its obstructions -/

/-- CAT-R lifting: no fibre of a divisorial monoid on a base category can be
additively equivalent to a nontrivial additive group, because
`DivisorialAddMonoid` fibres are sharp (Frobenioids I, section 0 and
Definition 1.1, (i): the unique unit is zero).  This lifts
`no_divisorialAddMonoid_of_addEquiv` from a single monoid to the fibre of any
`DivisorialMonoidOn`, i.e. to the categorical skeleton layer, and so
excludes the current group-valued prime-strip carriers from the divisorial
(sharp) input demanded by `Cv`/`C⊢v` regardless of the functorial
structure.  The target group is quantified at universe `Type`, matching the
universe of the existing lemma `no_divisorialAddMonoid_of_addEquiv`. -/
theorem no_divisorialMonoidOn_fibre_of_addEquiv
    {D : Type u} [Category.{u} D]
    {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    (Phi : Iut.DivisorialMonoidOn D IsFSM) (X : D)
    {G : Type} [AddGroup G] {g : G} (hg : g ≠ 0) :
    ¬ Nonempty ((Phi.obj X).carrier ≃+ G) :=
  fun ⟨e⟩ => no_divisorialAddMonoid_of_addEquiv hg ⟨Phi.obj X, ⟨e⟩⟩

/-- CAT-R weakest-skeleton statement: at fixed value kernels, a
`PrimeStripFrobenioidLinkLayer` exists if and only if the two directional
cards exist.  This shows the frozen contract is neither weaker nor stronger
than the card pair: any layer yields `ModDirectionCard` and
`MODDirectionCard` from its own maps, and the cards assemble a layer
(compare `primeStripFrobenioidLinkLayer_nonempty_of_cards`).  Source shape:
IUT I, Example 3.5, (i), the restriction functors `Cρv` and their degree
compatibility. -/
theorem primeStripFrobenioidLinkLayer_exists_iff_cards
    {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
    (localKernel : FrobenioidValueKernel X) (globalKernel : FrobenioidValueKernel Y) :
    (ModDirectionCard localKernel globalKernel ∧
        MODDirectionCard localKernel globalKernel) ↔
      ∃ L : PrimeStripFrobenioidLinkLayer X Y,
        L.localFrobenioid = localKernel ∧ L.globalFrobenioid = globalKernel := by
  constructor
  · rintro ⟨⟨modMap, hmod_degree, hmod_transport⟩, ⟨MODMap, hMOD_degree, hMOD_transport⟩⟩
    exact ⟨{ localFrobenioid := localKernel
             globalFrobenioid := globalKernel
             modMap := modMap
             MODMap := MODMap
             mod_degree := hmod_degree
             MOD_degree := hMOD_degree
             mod_transport := hmod_transport
             MOD_transport := hMOD_transport }, rfl, rfl⟩
  · rintro ⟨L, hl, hg⟩
    constructor
    · refine ⟨L.modMap, ?_, ?_⟩
      · intro x
        rw [← hg, ← hl]
        exact L.mod_degree x
      · intro x
        rw [← hl, ← hg]
        exact L.mod_transport x
    · refine ⟨L.MODMap, ?_, ?_⟩
      · intro y
        rw [← hl, ← hg]
        exact L.MOD_degree y
      · intro y
        rw [← hg, ← hl]
        exact L.MOD_transport y

/-- The contract is consistent: taking the same kernel on both sides with the
identity maps realizes the link layer.  The no-go statements below are
therefore about specific model couplings, not about a contradictory
contract. -/
theorem primeStripFrobenioidLinkLayer_self_inhabited {X : Type ux} [CommMonoid X]
    (k : FrobenioidValueKernel X) :
    Nonempty (PrimeStripFrobenioidLinkLayer X X) :=
  ⟨{ localFrobenioid := k
     globalFrobenioid := k
     modMap := id
     MODMap := id
     mod_degree := fun _ => rfl
     MOD_degree := fun _ => rfl
     mod_transport := fun _ => rfl
     MOD_transport := fun _ => rfl }⟩

/-- Derived no-go (CAT-R/MOD boundary of the finite model): the finite-place
model of `PrimeStripsFrobenioidLinks.lean` cannot support the reduced consumer
skeleton, because the MOD direction fails for its degree kernels
(`finitePlaceModel_not_MODDirectionCard` of `PrimeStripFrobenioidCards`).  The
finite model therefore must not be inflated to a general prime-strip
output. -/
theorem no_primeStripFrobenioidLinkLayer_finitePlaceModel
    (s : Finset RationalPrimePlace) (v0 : {v : RationalPrimePlace // v ∈ s}) :
    ¬ ∃ L : PrimeStripFrobenioidLinkLayer (frobenioidLinkIntegralStrip.Mon v0.1)
        (FinitePlaceValueFamily s),
      L.localFrobenioid = localIntegralPlaceFrobenioidValueKernel v0.1 ∧
        L.globalFrobenioid = finitePlaceFrobenioidValueKernel s := by
  rintro ⟨L, hl, hg⟩
  have hcards :
      ModDirectionCard (localIntegralPlaceFrobenioidValueKernel v0.1)
          (finitePlaceFrobenioidValueKernel s) ∧
        MODDirectionCard (localIntegralPlaceFrobenioidValueKernel v0.1)
          (finitePlaceFrobenioidValueKernel s) :=
    (primeStripFrobenioidLinkLayer_exists_iff_cards
      (localIntegralPlaceFrobenioidValueKernel v0.1)
      (finitePlaceFrobenioidValueKernel s)).mpr ⟨L, hl, hg⟩
  exact finitePlaceModel_not_MODDirectionCard s v0 hcards.2

/-! ## 2. MOD-R: the norm-image card of `ℚ̄p` -/

/-- `p^ℚ = {p^q | q : ℚ} ⊆ ℝ`, the candidate norm image at the place `p`
(real-exponentiation form: `p^q = exp(q · log p)`). -/
def padicPowSet (p : ℕ) : Set ℝ :=
  Set.range (fun q : ℚ => (p : ℝ) ^ (q : ℝ))

/-- The norm image of the units of `ℚ̄p` (that is, of
`AlgebraicClosure ℚ_[p]`), as a subset of `ℝ`. -/
def padicAlgClNormImage (p : ℕ) [Fact (Nat.Prime p)] : Set ℝ :=
  Set.range (fun u : (PadicAlgCl p)ˣ => ‖(u : PadicAlgCl p)‖)

/-- MOD-R frozen statement (reduced form at the local field): the norm image
of `(ℚ̄p)^×` is exactly `p^ℚ`.  This is the local arithmetic content behind
the MOD direction: it shows that the norm/degree image at one place is a
countable dense subset of `(0,∞)` and not an interval
(`not_surjective_padicPow`), so no single place can surject onto the
total-degree range of a multi-place family (compare
`finitePlaceModel_not_MODDirectionCard` of `PrimeStripFrobenioidCards`). -/
def PadicNormImageCard (p : ℕ) [Fact (Nat.Prime p)] : Prop :=
  padicAlgClNormImage p = padicPowSet p

/-- The arithmetic-surjectivity half of `PadicNormImageCard`: every rational
power `p^q` occurs as a norm. -/
def PadicNormImageSurjective (p : ℕ) [Fact (Nat.Prime p)] : Prop :=
  padicPowSet p ⊆ padicAlgClNormImage p

/-- The rationality half of `PadicNormImageCard`: every norm is a rational
power of `p`. -/
def PadicNormImageRational (p : ℕ) [Fact (Nat.Prime p)] : Prop :=
  padicAlgClNormImage p ⊆ padicPowSet p

/-- The frozen statement splits into its two halves. -/
theorem padicNormImageCard_iff (p : ℕ) [Fact (Nat.Prime p)] :
    PadicNormImageCard p ↔ PadicNormImageRational p ∧ PadicNormImageSurjective p := by
  unfold PadicNormImageCard PadicNormImageRational PadicNormImageSurjective
  exact Set.Subset.antisymm_iff

/-- `p^ℚ` is countable (countable parameter set), in contrast with `ℝ`. -/
theorem padicPowSet_countable (p : ℕ) : (padicPowSet p).Countable :=
  Set.countable_range (fun q : ℚ => (p : ℝ) ^ (q : ℝ))

/-- Counting statement: `q ↦ p^q` cannot be surjective onto `ℝ`, since its
range is countable while `ℝ` is not.  In particular `p^ℚ` is a proper
countable subset of `ℝ`. -/
theorem not_surjective_padicPow (p : ℕ) :
    ¬ Function.Surjective (fun q : ℚ => (p : ℝ) ^ (q : ℝ)) := by
  intro h
  have hcount : (Set.range (fun q : ℚ => (p : ℝ) ^ (q : ℝ))).Countable :=
    Set.countable_range _
  rw [Set.range_eq_univ.mpr h] at hcount
  exact Set.not_countable_univ hcount

/-- Density layer: between any two positive reals there is a rational power
of `p` (for `1 < p`).  Proof: logarithms transport the statement to the
density of `ℚ` in `ℝ` around `(log a)/log p`. -/
theorem exists_padicPow_between (p : ℕ) (hp : 1 < p) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    ∃ q : ℚ, a < (p : ℝ) ^ (q : ℝ) ∧ (p : ℝ) ^ (q : ℝ) < b := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hcpos : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hlog : Real.log a < Real.log b := Real.log_lt_log ha hab
  have hdiv : Real.log a / Real.log (p : ℝ) < Real.log b / Real.log (p : ℝ) :=
    div_lt_div_of_pos_right hlog hcpos
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hdiv
  refine ⟨q, ?_, ?_⟩
  · have hqa : Real.log a < (q : ℝ) * Real.log (p : ℝ) := by
      have h1 : (Real.log a / Real.log (p : ℝ)) * Real.log (p : ℝ)
          < (q : ℝ) * Real.log (p : ℝ) := mul_lt_mul_of_pos_right hq1 hcpos
      have h2 : (Real.log a / Real.log (p : ℝ)) * Real.log (p : ℝ) = Real.log a :=
        div_mul_cancel₀ _ (ne_of_gt hcpos)
      linarith [h1, h2]
    calc a = Real.exp (Real.log a) := (Real.exp_log ha).symm
      _ < Real.exp ((q : ℝ) * Real.log (p : ℝ)) := Real.exp_lt_exp.mpr hqa
      _ = (p : ℝ) ^ (q : ℝ) := by
            rw [Real.rpow_def_of_pos hp0]
            congr 1
            ring
  · have hqb : (q : ℝ) * Real.log (p : ℝ) < Real.log b := by
      have h1 : (q : ℝ) * Real.log (p : ℝ)
          < (Real.log b / Real.log (p : ℝ)) * Real.log (p : ℝ) :=
        mul_lt_mul_of_pos_right hq2 hcpos
      have h2 : (Real.log b / Real.log (p : ℝ)) * Real.log (p : ℝ) = Real.log b :=
        div_mul_cancel₀ _ (ne_of_gt hcpos)
      linarith [h1, h2]
    calc (p : ℝ) ^ (q : ℝ) = Real.exp ((q : ℝ) * Real.log (p : ℝ)) := by
            rw [Real.rpow_def_of_pos hp0]
            congr 1
            ring
      _ < Real.exp (Real.log b) := Real.exp_lt_exp.mpr hqb
      _ = b := Real.exp_log (lt_trans ha hab)

/-- The root computation behind the norm-surjectivity half: for `b > 0` there
is `y` with `y^b = p` and `‖y‖ = p^(-1/b)`.  The norm equation is obtained
from `‖y‖^b = ‖y^b‖ = ‖p‖ = p⁻¹` by taking logarithms; the nonzeroness of
`y` is not needed here, only when the unit is formed in
`padicAlgClNormImage_surjective`. -/
theorem exists_padicAlgCl_root_norm (p : ℕ) [Fact (Nat.Prime p)]
    (b : ℕ) (hb : 0 < b) :
    ∃ y : PadicAlgCl p, y ^ b = ((p : ℚ_[p]) : PadicAlgCl p) ∧
      ‖y‖ = (p : ℝ) ^ ((-1 : ℝ) / (b : ℝ)) := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((p : ℚ_[p]) : PadicAlgCl p) hb
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hnorm_pow : ‖y‖ ^ b = (p : ℝ)⁻¹ := by
    rw [← norm_pow]
    rw [hy, PadicAlgCl.norm_extends, Padic.norm_p]
  have hlog : (b : ℝ) * Real.log ‖y‖ = -Real.log (p : ℝ) := by
    rw [← Real.log_pow, hnorm_pow, Real.log_inv]
  have hlog' : Real.log ‖y‖ = -(Real.log (p : ℝ)) / (b : ℝ) := by
    rw [eq_div_iff (by exact_mod_cast (Nat.pos_iff_ne_zero.mp hb))]
    rw [mul_comm]
    exact hlog
  have hlogp_ne : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hp1)
  have hnorm_ne : ‖y‖ ≠ 0 := by
    intro h0
    have hz : Real.log ‖y‖ = 0 := by rw [h0, Real.log_zero]
    rw [hz] at hlog'
    have : -(Real.log (p : ℝ)) / (b : ℝ) ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr hlogp_ne)
        (by exact_mod_cast (Nat.pos_iff_ne_zero.mp hb))
    exact this hlog'.symm
  have hpos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg y) (Ne.symm hnorm_ne)
  refine ⟨y, hy, ?_⟩
  calc ‖y‖ = Real.exp (Real.log ‖y‖) := (Real.exp_log hpos).symm
    _ = Real.exp (Real.log (p : ℝ) * ((-1 : ℝ) / (b : ℝ))) := by
          rw [hlog']
          congr 1
          ring
    _ = (p : ℝ) ^ ((-1 : ℝ) / (b : ℝ)) := (Real.rpow_def_of_pos hp0 _).symm

/-- MOD-R minimal layer (proved): the arithmetic-surjectivity half of the
frozen card.  For every `q : ℚ`, `p^q` is the norm of a unit of `ℚ̄p`: take
the `b`-th root `y` of `p` (with `b` the denominator of `q`), so that
`‖y‖ = p^(-1/b)`, and raise it to the `(-num)` power. -/
theorem padicAlgClNormImage_surjective (p : ℕ) [Fact (Nat.Prime p)] :
    PadicNormImageSurjective p := by
  intro r hr
  obtain ⟨q, rfl⟩ := hr
  obtain ⟨y, hy, hy_norm⟩ := exists_padicAlgCl_root_norm p q.den q.den_pos
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hy_ne : y ≠ 0 := by
    rw [← norm_ne_zero_iff, hy_norm]
    exact ne_of_gt (Real.rpow_pos_of_pos hp0 _)
  refine ⟨Units.mk0 (y ^ (-(q.num))) (zpow_ne_zero _ hy_ne), ?_⟩
  change ‖y ^ (-(q.num))‖ = (p : ℝ) ^ (q : ℝ)
  have hval : ‖y ^ (-(q.num))‖ =
      (p : ℝ) ^ (((q.num : ℤ) : ℝ) / (q.den : ℝ)) := by
    rw [norm_zpow, hy_norm, ← Real.rpow_intCast, ← Real.rpow_mul (le_of_lt hp0)]
    congr 1
    push_cast
    ring
  rw [hval, Rat.cast_def]

/-- Density of the norm image in the positive reals (proved minimal layer):
between any two positive reals there is a norm of a unit of `ℚ̄p`, by
combining `exists_padicPow_between` with the surjectivity half. -/
theorem padicAlgClNormImage_dense_positives (p : ℕ) [Fact (Nat.Prime p)] :
    ∀ {a b : ℝ}, 0 < a → a < b →
      ∃ u : (PadicAlgCl p)ˣ, a < ‖(u : PadicAlgCl p)‖ ∧
        ‖(u : PadicAlgCl p)‖ < b := by
  intro a b ha hab
  obtain ⟨q, hq1, hq2⟩ :=
    exists_padicPow_between p (Fact.out : Nat.Prime p).one_lt ha hab
  obtain ⟨u, hu⟩ :=
    padicAlgClNormImage_surjective p (Set.mem_range_self q)
  have hu_norm : ‖(u : PadicAlgCl p)‖ = (p : ℝ) ^ (q : ℝ) := by simpa using hu
  exact ⟨u, by rw [hu_norm]; exact hq1, by rw [hu_norm]; exact hq2⟩

/-- MOD-R on the frozen carrier: the degree image of the unit-strip carrier
`frobenioidLinkUnitStrip` at `v` (degree = log of the norm, cf.
`inversePrimeUnit_degree`) contains *every* rational multiple of `log p`,
upgrading the single-unit computation `degree(inversePrimeUnit v) = log p` of
`PrimeStripFrobenioidCards` to all of `ℚ · log p`. -/
theorem frobenioidLinkUnitStrip_degreeImage_ratLog (v : RationalPrimePlace) :
    Set.range (fun q : ℚ => (q : ℝ) * Real.log (v.1 : ℝ)) ⊆
      Set.range (fun u : frobenioidLinkUnitStrip.Mon v =>
        (frobenioidLinkUnitStrip.degree v u).toAdd) := by
  intro r hr
  obtain ⟨q, rfl⟩ := hr
  letI : Fact (Nat.Prime v.1) := Fact.mk v.2
  have hp0 : (0 : ℝ) < (v.1 : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime v.1).pos
  obtain ⟨u, hu⟩ := padicAlgClNormImage_surjective v.1 (Set.mem_range_self q)
  refine ⟨u, ?_⟩
  change Real.log ‖(u : AlgebraicClosure ℚ_[v.1])‖ = (q : ℝ) * Real.log (v.1 : ℝ)
  have hu_norm : ‖(u : AlgebraicClosure ℚ_[v.1])‖ = (v.1 : ℝ) ^ (q : ℝ) := by simpa using hu
  rw [hu_norm, Real.log_rpow hp0]

end LeanFormal.IUT

end

namespace LeanFormal.IUT.Audit

/-- CAT-R / MOD-R round for `IUT-I-II.prime-strips-frobenioids`: the link-layer
skeleton biconditional, the finite-model no-go, and the norm-image card of
`PadicAlgCl` with its proved minimal layers (arithmetic surjectivity of the
norm onto `p^ℚ`, counting, density, degree-image upgrade). -/
def primeStripFrobenioidSkeletonCards : Obligation :=
  { id := "IUT-II.prime-strips-frobenioid-skeleton-cards"
    source :=
      "IUT I, Example 3.3, (i); Example 3.5, (i); Definition 5.2, (i)-(iv); " ++
        "IUT III, Example 3.6, (i)-(iii); Frobenioids I, section 0 and " ++
        "Definition 1.1, (i)"
    status := VerificationStatus.interface
    note :=
      "CAT-R / MOD-R round on top of `IUT-II.prime-strips-frobenioid-card-reductions`. " ++
        "CAT-R: the consumer skeleton `PrimeStripFrobenioidLinkLayer` is proved to be exactly " ++
        "the card pair at fixed kernels (`primeStripFrobenioidLinkLayer_exists_iff_cards`); " ++
        "the missing categorical input is the sharp divisorial monoid of effective geometric " ++
        "divisors, impossible for the current group-valued carriers even on any fibre of a " ++
        "`DivisorialMonoidOn` (`no_divisorialMonoidOn_fibre_of_addEquiv`); the finite-place " ++
        "model cannot support the reduced skeleton " ++
        "(`no_primeStripFrobenioidLinkLayer_finitePlaceModel`). MOD-R: the norm-image card " ++
        "`PadicNormImageCard` at `(Qbar_p)^x` is frozen and split into its two halves; the " ++
        "arithmetic-surjectivity half is PROVED (`padicAlgClNormImage_surjective`, so p^Q is " ++
        "contained in the norm image), together with the counting statements " ++
        "(`padicPowSet_countable`, `not_surjective_padicPow`), the density layer " ++
        "(`exists_padicPow_between`, `padicAlgClNormImage_dense_positives`), and the " ++
        "degree-image upgrade `frobenioidLinkUnitStrip_degreeImage_ratLog` (the degree image " ++
        "of the unit strip at v contains all of Q * log p). The rationality half and the " ++
        "torsor / fractional-ideal representations of IUT III, Example 3.6 remain parked " ++
        "with recorded cards. Boundary (1), (2), (4) specs are recorded in the module header. " ++
        "Consumers: K2FrobenioidBoundary, the Theorem 3.11 source chain, SourceHodgeTheaterBridge."
    dependsOn :=
      [ "IUT-II.prime-strips-frobenioid-card-reductions",
        "IUT-II.prime-strips-frobenioid-link-layer" ] }

end LeanFormal.IUT.Audit