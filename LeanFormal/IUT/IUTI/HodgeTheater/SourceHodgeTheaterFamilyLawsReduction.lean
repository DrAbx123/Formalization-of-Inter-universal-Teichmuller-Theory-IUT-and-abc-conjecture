/-
  Reduction pass for the source-facing Hodge-theater family laws.

  Paper anchor (`D:\lean\papers\motizuki_corpus\text\Inter-universal
  Teichmuller Theory I.txt`):

  * Definition 3.6: relative to a fixed initial Theta-data, a Theta-Hodge
    theater is a *data family* `({†F_v}_{v in V}, †F^⊩_mod)` satisfying (a)-(c).
  * Corollary 3.7 (i): between any two Theta-Hodge theaters over the same
    initial Theta-data the family of full poly-isomorphisms `†F^⊩_tht ~>
    ‡F^⊩_mod` is nonempty; a choice is a Theta-link.  Remark 3.7.1: many
    mutually indistinguishable isomorphisms exist.
  * Corollary 3.8: the source labels the theaters by `Z` (`{nHT^Theta}`),
    links adjacent pairs into an infinite chain, and allows the `Z`-translation
    symmetry while *excluding* arbitrary permutations of the chain.
    Remark 3.8.1 (i): the Theta-link carries `n Theta_v |-> (n+1) q_v`.
  * Theorem A (iii), Corollary 4.12 (iii), Corollary 6.10 (iii): the
    etale-picture description allows arbitrary permutations among the spokes
    over the mono-analytic core.
  * Definition 6.13: a Theta^{+-ell}NF-Hodge theater is a triple of a
    Theta^{+-ell} theater, a Theta^NF theater, and a gluing isomorphism.

  Frozen obligations addressed by this file:

  * `IUT-I.hodge-theater-family-source-laws` (`SourceHodgeTheaterFamily.lean`):
    a family of actual `HodgeTheater`s over an arbitrary index type, with
    injectivity, pairwise links, identity/symmetry/composition laws, and
    permutation naturality.
  * `IUT-I.hodge-theater-histories` (`InitialTheta/SourceObligations.lean:63`):
    "Construct distinct histories and their links; do not use an unconstrained
    record."
  * `IUT-I.hodge-theater-source` (`HodgeTheater/SourceObligations.lean`).

  Proved in this file:

  1. Contract consequences: every family carries one common theta packet on
     all members; members agreeing on arithmetic data and prime strip
     coincide; a constant-theater family forces a subsingleton index; two
     distinct indices yield a two-step dependent history whose terminal
     differs from its source (the source's `distinctness` field in action).
  2. A negative control: the unconstrained labeling record (index and theater
     only, no injectivity) carries the constant `Bool`-labeling, and its
     theater map is not injective; conversely a family with a constant
     theater map can only be indexed by a subsingleton, so no `Bool`-indexed
     constant labeling is a family.  This is how the "unconstrained record"
     prohibition is implemented: the `distinct` field is load-bearing.
  3. A genuinely distinct pair of concrete theaters sharing one prime strip
     and one theta packet: the Gaussian `y^2 + y = x^3` model of
     `gaussianInitialThetaArithmeticData` and a `j = 1728` model
     (`ofJ 1728 = ofJ1728`, `y^2 = x^3 + x`), separated by the `a_3`
     coefficient (`1` versus `0`).  These give `Bool`-indexed witness families
     that satisfy every law of `SourceHodgeTheaterFamily`, including a
     nontrivial permutation (swap) with its naturality square.
  4. A non-reflexive dependent history for the witness family, and a concrete
     initial-Theta history whose source and target carriers are distinct
     (`gaussianJ1728DistinctInitialThetaHistory`).

  Remaining source obligations (cards; not asserted here):

  * Constructing `{nHT^Theta}_{n in Z}` from arbitrary initial Theta-data
    (the Theorem A (i) / Corollary 3.8 construction) is not formalized; the
    witness family is finite (`Bool`) and is not the `Z`-chain.
  * The actual Theta-link map `n Theta_v |-> (n+1) q_v` on prime strips, the
    `Z`-translation action, and the source's exclusion of arbitrary chain
    permutations are not formalized; the `permutation` field of the contract
    models the etale-picture symmetry (Theorem A (iii)) at the level of an
    arbitrary index type only.
  * The Galois/etale theta, Hodge-Arakelov, and gluing data of Definition 6.13
    remain obligations of later modules.
-/

import LeanFormal.IUT.IUTI.HodgeTheater.SourceHodgeTheaterFamily
import LeanFormal.IUT.IUTI.HodgeTheater.ConcreteHodgeTheaterExample
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteInitialThetaLinks
import Init.Omega

set_option linter.checkUnivs false

namespace LeanFormal.IUT

noncomputable section

universe ua uv upi umon ui

local instance primeFactForFamilyLaws (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

local instance gaussianPolynomialIrreducibleFamilyLaws :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-! ## 1. Consequences of the family contract -/

namespace SourceHodgeTheaterFamily

variable {l : PrimeGeFive} {V : Type*}

theorem thetaPacket_eq (F : SourceHodgeTheaterFamily l V) (i j : F.index) :
    (F.theater i).thetaPacket = (F.theater j).thetaPacket := by
  have hq : (F.theater i).thetaPacket.q = (F.theater j).thetaPacket.q := F.link_q i j
  have hs : (F.theater i).thetaPacket.scale = (F.theater j).thetaPacket.scale :=
    funext (F.link_scale i j)
  generalize hθi : (F.theater i).thetaPacket = θᵢ at *
  generalize hθj : (F.theater j).thetaPacket = θⱼ at *
  obtain ⟨qᵢ, pᵢ, sᵢ, eᵢ⟩ := θᵢ
  obtain ⟨qⱼ, pⱼ, sⱼ, eⱼ⟩ := θⱼ
  dsimp only at hq hs
  cases hq
  cases hs
  rfl

theorem theater_eq_of_arithmetic_primeStrip_eq (F : SourceHodgeTheaterFamily l V)
    (i j : F.index)
    (h₁ : (F.theater i).arithmetic = (F.theater j).arithmetic)
    (h₂ : (F.theater i).primeStrip = (F.theater j).primeStrip) :
    F.theater i = F.theater j := by
  have hθ := F.thetaPacket_eq i j
  calc F.theater i
      = ⟨(F.theater i).arithmetic, (F.theater i).primeStrip,
          (F.theater i).thetaPacket⟩ := rfl
    _ = ⟨(F.theater j).arithmetic, (F.theater j).primeStrip,
          (F.theater j).thetaPacket⟩ := by
        rw [h₁, h₂, hθ]
    _ = F.theater j := rfl

theorem index_eq_of_arithmetic_primeStrip_eq (F : SourceHodgeTheaterFamily l V)
    (i j : F.index)
    (h₁ : (F.theater i).arithmetic = (F.theater j).arithmetic)
    (h₂ : (F.theater i).primeStrip = (F.theater j).primeStrip) :
    i = j :=
  F.distinct (F.theater_eq_of_arithmetic_primeStrip_eq i j h₁ h₂)

theorem theater_ne_of_ne (F : SourceHodgeTheaterFamily l V) {i j : F.index}
    (h : i ≠ j) : F.theater i ≠ F.theater j :=
  fun hh => h (F.distinct hh)

theorem subsingleton_index_of_constant_theater (F : SourceHodgeTheaterFamily l V)
    (h : ∀ i j, F.theater i = F.theater j) : Subsingleton F.index :=
  ⟨fun i j => F.distinct (h i j)⟩

theorem not_constant_theater_of_ne (F : SourceHodgeTheaterFamily l V)
    {i j : F.index} (h : i ≠ j) :
    ¬ (∀ a b : F.index, F.theater a = F.theater b) :=
  fun hc => h (F.distinct (hc i j))

theorem permutation_theater_ne (F : SourceHodgeTheaterFamily l V) {i : F.index}
    (h : F.permutation i ≠ i) :
    F.theater (F.permutation i) ≠ F.theater i :=
  fun hh => h (F.distinct hh)

def twoStepHistoryAt (F : SourceHodgeTheaterFamily l V) (i j : F.index) :
    HodgeTheaterHistory l V (F.theater i) :=
  .cons (F.link i j) (.singleton (F.theater j))

theorem twoStepHistoryAt_terminal (F : SourceHodgeTheaterFamily l V)
    (i j : F.index) :
    (F.twoStepHistoryAt i j).terminal = F.theater j := rfl

theorem twoStepHistoryAt_length (F : SourceHodgeTheaterFamily l V)
    (i j : F.index) :
    (F.twoStepHistoryAt i j).length = 2 := rfl

theorem twoStepHistoryAt_composite (F : SourceHodgeTheaterFamily l V)
    (i j : F.index) :
    (F.twoStepHistoryAt i j).composite = F.link i j :=
  HodgeTheaterLink.trans_refl (F.link i j)

theorem twoStepHistoryAt_source_ne_terminal (F : SourceHodgeTheaterFamily l V)
    {i j : F.index} (h : i ≠ j) :
    F.theater i ≠ (F.twoStepHistoryAt i j).terminal := by
  rw [F.twoStepHistoryAt_terminal]
  exact F.theater_ne_of_ne h

theorem twoStepHistoryAt_ne_singleton (F : SourceHodgeTheaterFamily l V)
    {i j : F.index} (_h : i ≠ j) :
    F.twoStepHistoryAt i j ≠ HodgeTheaterHistory.singleton (F.theater i) := by
  intro hh
  have hlen := congrArg HodgeTheaterHistory.length hh
  simp only [F.twoStepHistoryAt_length,
    HodgeTheaterHistory.length_singleton] at hlen
  omega

end SourceHodgeTheaterFamily

/-! ## 2. Negative control: the unconstrained labeling record -/

structure UnconstrainedTheaterLabeling (l : PrimeGeFive) (V : Type uv) where
  index : Type ui
  theater : index → HodgeTheater.{ua, uv, upi, umon} l V

def repeatedGaussianIntegralLabeling (l : PrimeGeFive) :
    UnconstrainedTheaterLabeling l (FinitePrimePlace 2 7) where
  index := Bool
  theater := fun _ => gaussianFiniteIntegralHodgeTheater l

theorem repeatedGaussianIntegralLabeling_not_injective (l : PrimeGeFive) :
    ¬ Function.Injective (repeatedGaussianIntegralLabeling l).theater := by
  intro h
  have h₁ : (repeatedGaussianIntegralLabeling l).theater false =
      (repeatedGaussianIntegralLabeling l).theater true := rfl
  exact Bool.false_ne_true (h h₁)

theorem repeatedGaussianIntegralLabeling_not_admissible (l : PrimeGeFive)
    (F : SourceHodgeTheaterFamily l (FinitePrimePlace 2 7))
    (e : F.index ≃ Bool)
    (hconst : ∀ i j, F.theater i = F.theater j) : False := by
  haveI : Subsingleton F.index :=
    F.subsingleton_index_of_constant_theater hconst
  haveI : Subsingleton Bool :=
    ⟨fun a b => by
      calc a = e (e.symm a) := (Equiv.apply_symm_apply e a).symm
        _ = e (e.symm b) :=
          congrArg e (Subsingleton.elim (e.symm a) (e.symm b))
        _ = b := Equiv.apply_symm_apply e b⟩
  exact Bool.false_ne_true (Subsingleton.elim false true)

/-! ## 3. A second arithmetic input: the `j = 1728` Gaussian curve -/

noncomputable def gaussianJ1728PuncturedCurve :
    PuncturedEllipticCurve GaussianField := by
  let model := ellipticModelWithJ (1728 : GaussianField)
  exact
    { curve := model.1
      isElliptic := model.2
      puncture := ⟨WeierstrassCurve.Projective.nonsingularLift_zero⟩ }

theorem gaussianJ1728PuncturedCurve_curve :
    gaussianJ1728PuncturedCurve.curve =
      WeierstrassCurve.ofJ (1728 : GaussianField) := rfl

theorem gaussianPuncturedCurve_curve :
    gaussianPuncturedCurve.curve = WeierstrassCurve.ofJ (0 : GaussianField) := rfl

theorem gaussianPuncturedCurve_curve_eq_ofJ0 :
    gaussianPuncturedCurve.curve = WeierstrassCurve.ofJ0 GaussianField := by
  rw [gaussianPuncturedCurve_curve]
  exact WeierstrassCurve.ofJ_0_of_three_ne_zero (by norm_num)

theorem gaussianJ1728PuncturedCurve_curve_eq_ofJ1728 :
    gaussianJ1728PuncturedCurve.curve =
      WeierstrassCurve.ofJ1728 GaussianField := by
  rw [gaussianJ1728PuncturedCurve_curve]
  exact WeierstrassCurve.ofJ_1728_of_two_ne_zero (by norm_num)

theorem ofJ0_ne_ofJ1728_gaussianField :
    WeierstrassCurve.ofJ0 GaussianField ≠
      WeierstrassCurve.ofJ1728 GaussianField := by
  intro h
  have h₁ : (1 : GaussianField) = 0 := by
    simpa [WeierstrassCurve.ofJ0, WeierstrassCurve.ofJ1728] using
      congrArg WeierstrassCurve.a₃ h
  exact one_ne_zero h₁

theorem gaussianPuncturedCurve_ne_gaussianJ1728PuncturedCurve :
    gaussianPuncturedCurve ≠ gaussianJ1728PuncturedCurve := by
  intro h
  refine ofJ0_ne_ofJ1728_gaussianField ?_
  have hc : gaussianPuncturedCurve.curve = gaussianJ1728PuncturedCurve.curve :=
    congrArg (fun E : PuncturedEllipticCurve GaussianField => E.curve) h
  rw [gaussianPuncturedCurve_curve_eq_ofJ0,
    gaussianJ1728PuncturedCurve_curve_eq_ofJ1728] at hc
  exact hc

def gaussianJ1728ArithmeticData (l : PrimeGeFive) :
    InitialThetaArithmeticData l where
  Fmod := GaussianField
  F := GaussianField
  K := GaussianField
  tower := gaussianIdentityThetaTower l
  curve := gaussianJ1728PuncturedCurve

@[simp] theorem gaussianJ1728ArithmeticData_curve (l : PrimeGeFive) :
    (gaussianJ1728ArithmeticData l).curve = gaussianJ1728PuncturedCurve := rfl

@[simp] theorem gaussianInitialThetaArithmeticData_curve (l : PrimeGeFive) :
    (gaussianInitialThetaArithmeticData l).curve = gaussianPuncturedCurve := rfl

theorem gaussianJ1728Curves_eq_of_arithmeticData_eq (l : PrimeGeFive)
    (h : gaussianJ1728ArithmeticData l = gaussianInitialThetaArithmeticData l) :
    gaussianJ1728PuncturedCurve = gaussianPuncturedCurve := by
  have hhe : HEq (gaussianJ1728ArithmeticData l).curve
      (gaussianInitialThetaArithmeticData l).curve :=
    @Eq.rec (InitialThetaArithmeticData l)
      (gaussianInitialThetaArithmeticData l)
      (fun X _ => HEq X.curve (gaussianInitialThetaArithmeticData l).curve)
      (HEq.refl (gaussianInitialThetaArithmeticData l).curve)
      (gaussianJ1728ArithmeticData l)
      h.symm
  have hc : (gaussianJ1728ArithmeticData l).curve =
      (gaussianInitialThetaArithmeticData l).curve := eq_of_heq hhe
  rwa [gaussianJ1728ArithmeticData_curve,
    gaussianInitialThetaArithmeticData_curve] at hc

theorem gaussianJ1728ArithmeticData_ne (l : PrimeGeFive) :
    gaussianJ1728ArithmeticData l ≠ gaussianInitialThetaArithmeticData l :=
  fun h => gaussianPuncturedCurve_ne_gaussianJ1728PuncturedCurve
    (gaussianJ1728Curves_eq_of_arithmeticData_eq l h).symm

def gaussianJ1728FiniteIntegralTheater (l : PrimeGeFive) :
    HodgeTheater l (FinitePrimePlace 2 7) where
  arithmetic := gaussianJ1728ArithmeticData l
  primeStrip := finiteLocalIntegralFPrimeStrip 2 7
  thetaPacket :=
    FiniteThetaPacket.ofQ (l := l) gaussianFiveThetaQ gaussianFiveThetaQ_pos

theorem gaussianJ1728FiniteIntegralTheater_ne (l : PrimeGeFive) :
    gaussianJ1728FiniteIntegralTheater l ≠
      gaussianFiniteIntegralHodgeTheater l := by
  intro h
  exact gaussianJ1728ArithmeticData_ne l
    (congrArg (fun T : HodgeTheater l (FinitePrimePlace 2 7) => T.arithmetic) h)

def gaussianJ1728RationalPlaceTheater (l : PrimeGeFive) :
    HodgeTheater l RationalPrimePlace where
  arithmetic := gaussianJ1728ArithmeticData l
  primeStrip := localFPrimeStrip
  thetaPacket := FiniteThetaPacket.ofQ (l := l) (1 / 2 : Real) (by norm_num)

theorem gaussianJ1728RationalPlaceTheater_ne (l : PrimeGeFive) :
    gaussianJ1728RationalPlaceTheater l ≠ gaussianHodgeTheater l := by
  intro h
  exact gaussianJ1728ArithmeticData_ne l
    (congrArg (fun T : HodgeTheater l RationalPrimePlace => T.arithmetic) h)

/-! ## 4. A two-member witness family satisfying every contract law -/

def hodgeTheaterSameStripLink {l : PrimeGeFive} {V : Type*}
    (A A' : InitialThetaArithmeticData l) (P : FPrimeStrip V)
    (θ : FiniteThetaPacket l) :
    HodgeTheaterLink (⟨A, P, θ⟩ : HodgeTheater l V) ⟨A', P, θ⟩ where
  primeStripEquiv := FPrimeStripEquiv.refl P
  theta_q_eq := rfl
  theta_scale_eq := fun _ => rfl

def twoTheaterWitnessTheater {l : PrimeGeFive} {V : Type*}
    (P : FPrimeStrip V) (θ : FiniteThetaPacket l)
    (A₀ A₁ : InitialThetaArithmeticData l) : Bool → HodgeTheater l V
  | false => ⟨A₀, P, θ⟩
  | true => ⟨A₁, P, θ⟩

theorem twoTheaterWitnessTheater_injective {l : PrimeGeFive} {V : Type*}
    (P : FPrimeStrip V) (θ : FiniteThetaPacket l)
    (A₀ A₁ : InitialThetaArithmeticData l) (h : A₀ ≠ A₁) :
    Function.Injective (twoTheaterWitnessTheater P θ A₀ A₁) := by
  intro i j hij
  cases i <;> cases j
  · rfl
  · exact absurd (congrArg (fun T : HodgeTheater l V => T.arithmetic) hij) h
  · exact absurd ((congrArg (fun T : HodgeTheater l V => T.arithmetic) hij).symm) h
  · rfl

def twoTheaterWitnessLink {l : PrimeGeFive} {V : Type*}
    (P : FPrimeStrip V) (θ : FiniteThetaPacket l)
    (A₀ A₁ : InitialThetaArithmeticData l) (i j : Bool) :
    HodgeTheaterLink (twoTheaterWitnessTheater P θ A₀ A₁ i)
      (twoTheaterWitnessTheater P θ A₀ A₁ j) := by
  cases i <;> cases j
  · exact hodgeTheaterSameStripLink A₀ A₀ P θ
  · exact hodgeTheaterSameStripLink A₀ A₁ P θ
  · exact hodgeTheaterSameStripLink A₁ A₀ P θ
  · exact hodgeTheaterSameStripLink A₁ A₁ P θ

theorem twoTheaterWitnessLink_refl {l : PrimeGeFive} {V : Type*}
    (P : FPrimeStrip V) (θ : FiniteThetaPacket l)
    (A₀ A₁ : InitialThetaArithmeticData l) (i : Bool) :
    twoTheaterWitnessLink P θ A₀ A₁ i i =
      HodgeTheaterLink.refl (twoTheaterWitnessTheater P θ A₀ A₁ i) := by
  cases i <;> rfl

theorem twoTheaterWitnessLink_symm {l : PrimeGeFive} {V : Type*}
    (P : FPrimeStrip V) (θ : FiniteThetaPacket l)
    (A₀ A₁ : InitialThetaArithmeticData l) (i j : Bool) :
    HodgeTheaterLink.symm (twoTheaterWitnessLink P θ A₀ A₁ i j) =
      twoTheaterWitnessLink P θ A₀ A₁ j i := by
  cases i <;> cases j <;> rfl

theorem twoTheaterWitnessLink_trans {l : PrimeGeFive} {V : Type*}
    (P : FPrimeStrip V) (θ : FiniteThetaPacket l)
    (A₀ A₁ : InitialThetaArithmeticData l) (i j k : Bool) :
    HodgeTheaterLink.trans (twoTheaterWitnessLink P θ A₀ A₁ i j)
        (twoTheaterWitnessLink P θ A₀ A₁ j k) =
      twoTheaterWitnessLink P θ A₀ A₁ i k := by
  cases i <;> cases j <;> cases k <;> rfl

def twoTheaterWitnessPermutation : Equiv.Perm Bool :=
  Equiv.swap false true

theorem twoTheaterWitnessPermutation_false :
    twoTheaterWitnessPermutation false = true := rfl

theorem twoTheaterWitnessPermutation_true :
    twoTheaterWitnessPermutation true = false := rfl

def twoTheaterWitnessPermutationLink {l : PrimeGeFive} {V : Type*}
    (P : FPrimeStrip V) (θ : FiniteThetaPacket l)
    (A₀ A₁ : InitialThetaArithmeticData l) (i : Bool) :
    HodgeTheaterLink
      (twoTheaterWitnessTheater P θ A₀ A₁ (twoTheaterWitnessPermutation i))
      (twoTheaterWitnessTheater P θ A₀ A₁ i) := by
  cases i
  · exact hodgeTheaterSameStripLink A₁ A₀ P θ
  · exact hodgeTheaterSameStripLink A₀ A₁ P θ

theorem twoTheaterWitnessPermutation_naturality {l : PrimeGeFive} {V : Type*}
    (P : FPrimeStrip V) (θ : FiniteThetaPacket l)
    (A₀ A₁ : InitialThetaArithmeticData l) (i j : Bool) :
    HodgeTheaterLink.trans
        (twoTheaterWitnessLink P θ A₀ A₁ (twoTheaterWitnessPermutation i)
          (twoTheaterWitnessPermutation j))
        (twoTheaterWitnessPermutationLink P θ A₀ A₁ j) =
      HodgeTheaterLink.trans (twoTheaterWitnessPermutationLink P θ A₀ A₁ i)
        (twoTheaterWitnessLink P θ A₀ A₁ i j) := by
  cases i <;> cases j <;> rfl

def twoTheaterWitnessFamily {l : PrimeGeFive} {V : Type*}
    (P : FPrimeStrip V) (θ : FiniteThetaPacket l)
    (A₀ A₁ : InitialThetaArithmeticData l) (h : A₀ ≠ A₁) :
    SourceHodgeTheaterFamily l V where
  index := Bool
  theater := twoTheaterWitnessTheater P θ A₀ A₁
  distinct := twoTheaterWitnessTheater_injective P θ A₀ A₁ h
  link := twoTheaterWitnessLink P θ A₀ A₁
  link_refl := twoTheaterWitnessLink_refl P θ A₀ A₁
  link_symm := twoTheaterWitnessLink_symm P θ A₀ A₁
  link_trans := twoTheaterWitnessLink_trans P θ A₀ A₁
  permutation := twoTheaterWitnessPermutation
  permutationLink := twoTheaterWitnessPermutationLink P θ A₀ A₁
  permutation_naturality := twoTheaterWitnessPermutation_naturality P θ A₀ A₁

def finiteIntegralTwoTheaterFamily (l : PrimeGeFive) :
    SourceHodgeTheaterFamily l (FinitePrimePlace 2 7) :=
  twoTheaterWitnessFamily (finiteLocalIntegralFPrimeStrip 2 7)
    (FiniteThetaPacket.ofQ (l := l) gaussianFiveThetaQ gaussianFiveThetaQ_pos)
    (gaussianInitialThetaArithmeticData l) (gaussianJ1728ArithmeticData l)
    (fun h => gaussianJ1728ArithmeticData_ne l h.symm)

def rationalPlaceTwoTheaterFamily (l : PrimeGeFive) :
    SourceHodgeTheaterFamily l RationalPrimePlace :=
  twoTheaterWitnessFamily localFPrimeStrip
    (FiniteThetaPacket.ofQ (l := l) (1 / 2 : Real) (by norm_num))
    (gaussianInitialThetaArithmeticData l) (gaussianJ1728ArithmeticData l)
    (fun h => gaussianJ1728ArithmeticData_ne l h.symm)

theorem finiteIntegralTwoTheaterFamily_theater_false (l : PrimeGeFive) :
    (finiteIntegralTwoTheaterFamily l).theater false =
      gaussianFiniteIntegralHodgeTheater l := rfl

theorem finiteIntegralTwoTheaterFamily_theater_true (l : PrimeGeFive) :
    (finiteIntegralTwoTheaterFamily l).theater true =
      gaussianJ1728FiniteIntegralTheater l := rfl

theorem finiteIntegralTwoTheaterFamily_theater_ne (l : PrimeGeFive) :
    (finiteIntegralTwoTheaterFamily l).theater false ≠
      (finiteIntegralTwoTheaterFamily l).theater true := by
  rw [finiteIntegralTwoTheaterFamily_theater_false,
    finiteIntegralTwoTheaterFamily_theater_true]
  exact fun h => gaussianJ1728FiniteIntegralTheater_ne l h.symm

theorem finiteIntegralTwoTheaterFamily_distinct (l : PrimeGeFive) :
    Function.Injective (finiteIntegralTwoTheaterFamily l).theater :=
  (finiteIntegralTwoTheaterFamily l).distinct

theorem finiteIntegralTwoTheaterFamily_link_refl_at (l : PrimeGeFive) :
    (finiteIntegralTwoTheaterFamily l).link false false =
      HodgeTheaterLink.refl ((finiteIntegralTwoTheaterFamily l).theater false) :=
  (finiteIntegralTwoTheaterFamily l).link_refl false

theorem finiteIntegralTwoTheaterFamily_link_symm_at (l : PrimeGeFive) :
    HodgeTheaterLink.symm ((finiteIntegralTwoTheaterFamily l).link false true) =
      (finiteIntegralTwoTheaterFamily l).link true false :=
  (finiteIntegralTwoTheaterFamily l).link_symm false true

theorem finiteIntegralTwoTheaterFamily_link_trans_at (l : PrimeGeFive) :
    HodgeTheaterLink.trans ((finiteIntegralTwoTheaterFamily l).link false true)
        ((finiteIntegralTwoTheaterFamily l).link true false) =
      (finiteIntegralTwoTheaterFamily l).link false false :=
  (finiteIntegralTwoTheaterFamily l).link_trans false true false

theorem finiteIntegralTwoTheaterFamily_link_q (l : PrimeGeFive) :
    ((finiteIntegralTwoTheaterFamily l).theater false).thetaPacket.q =
      ((finiteIntegralTwoTheaterFamily l).theater true).thetaPacket.q :=
  (finiteIntegralTwoTheaterFamily l).link_q false true

theorem finiteIntegralTwoTheaterFamily_link_scale (l : PrimeGeFive)
    (r : SignedLabel l.value) :
    ((finiteIntegralTwoTheaterFamily l).theater false).thetaPacket.scale r =
      ((finiteIntegralTwoTheaterFamily l).theater true).thetaPacket.scale r :=
  (finiteIntegralTwoTheaterFamily l).link_scale false true r

theorem finiteIntegralTwoTheaterFamily_thetaPacket_eq (l : PrimeGeFive) :
    ((finiteIntegralTwoTheaterFamily l).theater false).thetaPacket =
      ((finiteIntegralTwoTheaterFamily l).theater true).thetaPacket :=
  (finiteIntegralTwoTheaterFamily l).thetaPacket_eq false true

theorem finiteIntegralTwoTheaterFamily_arithmetic_ne (l : PrimeGeFive) :
    ((finiteIntegralTwoTheaterFamily l).theater false).arithmetic ≠
      ((finiteIntegralTwoTheaterFamily l).theater true).arithmetic := by
  rw [finiteIntegralTwoTheaterFamily_theater_false,
    finiteIntegralTwoTheaterFamily_theater_true]
  exact fun h => gaussianJ1728ArithmeticData_ne l h.symm

theorem finiteIntegralTwoTheaterFamily_permutation_false (l : PrimeGeFive) :
    (finiteIntegralTwoTheaterFamily l).permutation false = true :=
  twoTheaterWitnessPermutation_false

theorem finiteIntegralTwoTheaterFamily_permutation_naturality_at
    (l : PrimeGeFive) :
    HodgeTheaterLink.trans
        ((finiteIntegralTwoTheaterFamily l).link
          ((finiteIntegralTwoTheaterFamily l).permutation false)
          ((finiteIntegralTwoTheaterFamily l).permutation true))
        ((finiteIntegralTwoTheaterFamily l).permutationLink true) =
      HodgeTheaterLink.trans
        ((finiteIntegralTwoTheaterFamily l).permutationLink false)
        ((finiteIntegralTwoTheaterFamily l).link false true) :=
  (finiteIntegralTwoTheaterFamily l).permutation_naturality false true

def finiteIntegralTwoTheaterSystem (l : PrimeGeFive) :
    SourceThreeTheaterSystem (finiteIntegralTwoTheaterFamily l) where
  source := false
  middle := true
  target := false
  source_to_middle := (finiteIntegralTwoTheaterFamily l).link false true
  middle_to_target := (finiteIntegralTwoTheaterFamily l).link true false
  source_to_middle_eq_family := rfl
  middle_to_target_eq_family := rfl

theorem finiteIntegralTwoTheaterSystem_source_to_target (l : PrimeGeFive) :
    (finiteIntegralTwoTheaterSystem l).source_to_target =
      HodgeTheaterLink.refl ((finiteIntegralTwoTheaterFamily l).theater false) := by
  rw [(finiteIntegralTwoTheaterSystem l).source_to_target_link]
  exact (finiteIntegralTwoTheaterFamily l).link_refl_at false

theorem rationalPlaceTwoTheaterFamily_theater_false (l : PrimeGeFive) :
    (rationalPlaceTwoTheaterFamily l).theater false = gaussianHodgeTheater l := rfl

theorem rationalPlaceTwoTheaterFamily_theater_true (l : PrimeGeFive) :
    (rationalPlaceTwoTheaterFamily l).theater true =
      gaussianJ1728RationalPlaceTheater l := rfl

theorem rationalPlaceTwoTheaterFamily_theater_ne (l : PrimeGeFive) :
    (rationalPlaceTwoTheaterFamily l).theater false ≠
      (rationalPlaceTwoTheaterFamily l).theater true := by
  rw [rationalPlaceTwoTheaterFamily_theater_false,
    rationalPlaceTwoTheaterFamily_theater_true]
  exact fun h => gaussianJ1728RationalPlaceTheater_ne l h.symm

theorem rationalPlaceTwoTheaterFamily_link_q (l : PrimeGeFive) :
    ((rationalPlaceTwoTheaterFamily l).theater false).thetaPacket.q =
      ((rationalPlaceTwoTheaterFamily l).theater true).thetaPacket.q :=
  (rationalPlaceTwoTheaterFamily l).link_q false true

theorem rationalPlaceTwoTheaterFamily_permutation_naturality_at
    (l : PrimeGeFive) :
    HodgeTheaterLink.trans
        ((rationalPlaceTwoTheaterFamily l).link
          ((rationalPlaceTwoTheaterFamily l).permutation false)
          ((rationalPlaceTwoTheaterFamily l).permutation true))
        ((rationalPlaceTwoTheaterFamily l).permutationLink true) =
      HodgeTheaterLink.trans
        ((rationalPlaceTwoTheaterFamily l).permutationLink false)
        ((rationalPlaceTwoTheaterFamily l).link false true) :=
  (rationalPlaceTwoTheaterFamily l).permutation_naturality false true

/-! ## 5. Non-reflexive histories for the witness family -/

def finiteIntegralTwoTheaterHistory (l : PrimeGeFive) :
    HodgeTheaterHistory l (FinitePrimePlace 2 7)
      ((finiteIntegralTwoTheaterFamily l).theater false) :=
  (finiteIntegralTwoTheaterFamily l).twoStepHistoryAt false true

theorem finiteIntegralTwoTheaterHistory_terminal (l : PrimeGeFive) :
    (finiteIntegralTwoTheaterHistory l).terminal =
      (finiteIntegralTwoTheaterFamily l).theater true :=
  (finiteIntegralTwoTheaterFamily l).twoStepHistoryAt_terminal false true

theorem finiteIntegralTwoTheaterHistory_length (l : PrimeGeFive) :
    (finiteIntegralTwoTheaterHistory l).length = 2 :=
  (finiteIntegralTwoTheaterFamily l).twoStepHistoryAt_length false true

theorem finiteIntegralTwoTheaterHistory_composite (l : PrimeGeFive) :
    (finiteIntegralTwoTheaterHistory l).composite =
      (finiteIntegralTwoTheaterFamily l).link false true :=
  (finiteIntegralTwoTheaterFamily l).twoStepHistoryAt_composite false true

theorem finiteIntegralTwoTheaterHistory_source_ne_terminal (l : PrimeGeFive) :
    (finiteIntegralTwoTheaterFamily l).theater false ≠
      (finiteIntegralTwoTheaterHistory l).terminal :=
  (finiteIntegralTwoTheaterFamily l).twoStepHistoryAt_source_ne_terminal
    (by exact Bool.false_ne_true)

theorem finiteIntegralTwoTheaterHistory_ne_singleton (l : PrimeGeFive) :
    finiteIntegralTwoTheaterHistory l ≠
      HodgeTheaterHistory.singleton
        ((finiteIntegralTwoTheaterFamily l).theater false) :=
  (finiteIntegralTwoTheaterFamily l).twoStepHistoryAt_ne_singleton
    (by exact Bool.false_ne_true)

/-! ## 6. A distinct concrete initial-Theta history -/

def gaussianJ1728InitialThetaCarrier (l : PrimeGeFive) :
    ConcreteInitialThetaCarrier l where
  placeInput := concreteInitialThetaPlaceInput l
  theater := gaussianJ1728FiniteIntegralTheater l
  localCarrier := ConcreteTateLocalCarrier.canonical l
  selectedLabel := concreteInitialThetaLabel
  selectedLabel_eq_five := rfl

theorem gaussianJ1728InitialThetaCarrier_ne (l : PrimeGeFive) :
    gaussianJ1728InitialThetaCarrier l ≠ concreteInitialThetaCarrier l := by
  intro h
  have ht : (gaussianJ1728InitialThetaCarrier l).theater =
      (concreteInitialThetaCarrier l).theater :=
    congrArg (fun c : ConcreteInitialThetaCarrier l => c.theater) h
  exact gaussianJ1728FiniteIntegralTheater_ne l ht

def gaussianJ1728DistinctInitialThetaHistory (l : PrimeGeFive) :
    ConcreteInitialThetaHistory l where
  source := concreteInitialThetaCarrier l
  middle := concreteInitialThetaCarrier l
  target := gaussianJ1728InitialThetaCarrier l
  source_to_middle := rfl
  middle_to_target := rfl
  source_q_eq_middle := rfl
  middle_q_eq_target := rfl
  source_scale_eq_middle := fun _ => rfl
  middle_scale_eq_target := fun _ => rfl

theorem gaussianJ1728DistinctInitialThetaHistory_source_ne_target
    (l : PrimeGeFive) :
    (gaussianJ1728DistinctInitialThetaHistory l).source ≠
      (gaussianJ1728DistinctInitialThetaHistory l).target := by
  intro h
  exact gaussianJ1728InitialThetaCarrier_ne l h.symm

theorem gaussianJ1728DistinctInitialThetaHistory_ne_reflexive
    (l : PrimeGeFive) :
    gaussianJ1728DistinctInitialThetaHistory l ≠
      concreteInitialThetaHistory l := by
  intro h
  have ht : (gaussianJ1728DistinctInitialThetaHistory l).target =
      (concreteInitialThetaHistory l).target :=
    congrArg (fun H : ConcreteInitialThetaHistory l => H.target) h
  exact gaussianJ1728InitialThetaCarrier_ne l ht

namespace ConcreteInitialThetaHistory

variable {l : PrimeGeFive}

theorem primeStrip_eq (H : ConcreteInitialThetaHistory l) :
    H.source.theater.primeStrip = H.target.theater.primeStrip :=
  H.source_to_middle.trans H.middle_to_target

theorem q_eq (H : ConcreteInitialThetaHistory l) :
    H.source.theater.thetaPacket.q = H.target.theater.thetaPacket.q :=
  H.source_q_eq_middle.trans H.middle_q_eq_target

theorem scale_eq (H : ConcreteInitialThetaHistory l) (j : SignedLabel l.value) :
    H.source.theater.thetaPacket.scale j = H.target.theater.thetaPacket.scale j :=
  (H.source_scale_eq_middle j).trans (H.middle_scale_eq_target j)

end ConcreteInitialThetaHistory

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def hodgeTheaterFamilyLawsReduction : Obligation :=
  { id := "IUT-I.hodge-theater-family-laws-reduction"
    source :=
      "IUT I: Definition 3.6; Corollary 3.7 (i) and Remark 3.7.1; " ++
        "Corollary 3.8 and Remark 3.8.1 (i); Theorem A (iii); " ++
        "Corollaries 4.12 (iii), 6.10 (iii); Definition 6.13"
    status := VerificationStatus.interface
    note :=
      "Reduction pass for the frozen family/history source laws. Proved here: " ++
        "(1) contract consequences for any SourceHodgeTheaterFamily - a unique " ++
        "common theta packet, coincidence from equal arithmetic plus prime " ++
        "strip, subsingleton index for constant theater maps, and two-step " ++
        "non-reflexive dependent histories from any pair of distinct indices; " ++
        "(2) a negative control showing the unconstrained labeling record " ++
        "carries a constant Bool-labeling whose theater map is not injective; " ++
        "(3) a concrete distinct pair of theaters sharing one prime strip and " ++
        "theta packet (Gaussian y^2 + y = x^3 versus ofJ 1728 = y^2 = x^3 + x, " ++
        "separated by a_3 = 1 versus a_3 = 0) assembled into Bool-indexed " ++
        "witness families (finite integral and rational place carriers) that " ++
        "satisfy injectivity, link identity/symmetry/composition, and the " ++
        "swap permutation naturality; (4) a non-reflexive history for the " ++
        "finite-integral witness family and a concrete initial-Theta history " ++
        "with distinct source/target carriers. Not proved (source cards): the " ++
        "Z-indexed family {nHT^Theta} from arbitrary initial Theta-data, the " ++
        "actual Theta-link displacement n Theta_v |-> (n+1) q_v, the " ++
        "Z-translation/non-permutation structure of the Theta-chain, and the " ++
        "gluing data of Definition 6.13; the witness families are finite " ++
        "carrier tests and are not the source's Z-chain."
    dependsOn :=
      [ "IUT-I.hodge-theater-family-source-laws",
        "IUT-I.hodge-theater-histories",
        "IUT-I.hodge-theater-source" ] }

end LeanFormal.IUT.Audit
