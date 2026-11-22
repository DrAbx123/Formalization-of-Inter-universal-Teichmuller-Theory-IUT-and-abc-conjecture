/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S1978LocalFieldOCarrierActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtalePiOneKernelRealization
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveScheme
import LeanFormal.IUT.Foundations.Geometry.ConcreteTateParameter
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceUnitRegionHaarDataActual

/-!
# S2038: the actual paper O object: definition, constructed q-pilot, and the
exact first-missing chain

Layer: O (original Theta-link / q-pilot).  Assembly node of the
S1958/S1965/S1966/S1967/S1973/S1978/S1979 worker chain and of the
S2031/S2032/S2034/S2035/S2037 companion nodes.  It defines the paper O object
PaperOActual with the five components required by the source, constructs the
q-pilot component outright, and reduces the object to the exact bundle of
missing constructions.

## What the paper object is (IUT II, Definitions 1.1 and 4.9, Example 1.8)

PaperOActual has exactly these fields:

* (a) FPsiPrimeStrip: the actual F-double-plus-prime-strip.  Its local value
  monoids are the actual local O-times of the actual local fields (not the
  S1487 shear monoid SourceHaarActualValueMonoid, and not the reduced
  identity-projection strip localOFieldStrip), and its local groups carry an
  actual once-punctured elliptic curve with the tempered/etale fundamental
  groups and the functorial surjection onto the local absolute Galois group
  whose geometric kernel is nontrivial.
* (b) ThetaMonoidActual: the paper-level theta / Gaussian monoid assignment of
  IUT II, Corollary 4.6, (iv), over the fixed finite theta packet of the actual
  input, with the Gaussian evaluation of Proposition 4.1, (iv).  This is not
  the local-field model PsiEnvModel/PsiGauModel of S1973.
* (c) OUnitsMuActor: the group-theoretic actor O-times-mu(G) of IUT II,
  Example 1.8, (iii)--(iv): a construction depending only on the profinite
  group G, functorial under isomorphisms of profinite groups, evaluated at the
  actual local absolute Galois groups and identified with the actual local
  O-times-mu.
* (d) QPilotODaggerData: the actual q-pilot O-triangle generator, constructed
  in section 1 from the actual Tate parameter q = l
  (ConcreteTateParameter.canonical), with O-triangle isomorphic to N, an
  infinite-order generator, its integrality, and the theorem that it cannot be
  identified with the degenerate S1487 value monoid.
* (e) OperationKummerEvaluation: the operation-level Kummer isomorphism (IUT
  II, Definition 4.9, (i)) and evaluation isomorphism (IUT II, Corollary 4.10,
  (ii)) between the group-theoretic side O-times-mu(G_v) and the Frobenioid
  side O-times-mu of the actual local monoid.

## What is proved here (kernel-checked, no sorry, no axiom)

1. The construction of (d), with O-triangle isomorphic to N, a nontrivial
   infinite-order generator, integrality in the actual local O-triangle, and
   the formal impossibility not (Nonempty (O-triangle ~= SourceHaar)) of
   identifying it with the degenerate S1487 value monoid.
2. For every PaperOActual, the local monoids are the actual local O-times
   (fPsi_mon_not_sourceHaar), and its strip cannot be the reduced
   identity-projection strip localOFieldStrip
   (no_fPsi_equiv_localOFieldStrip): the geometric kernel is nontrivial on the
   paper side and trivial on the reduced side, and strip equivalence preserves
   triviality of the kernel.
3. The exact first missing chain: PaperOActual is nonempty exactly when the
   bundle PaperOFirstMissing of the four missing constructions is nonempty
   (nonempty_paperOActual_iff), and the first link of the chain is the missing
   actual curve pi_1 (firstMissing_curvePiOne).

## The exact first missing chain (no fake)

The first missing is not a proposition about existing carriers; it is a
missing construction.  In dependency order:

1. CurvePiOneData (component (a)): the actual etale and tempered fundamental
   groups of the once-punctured elliptic curve, with the nontrivial geometric
   kernel.  Mathlib 4.32.2 has the curve scheme curveScheme and the category of
   finite etale covers, but no Galois-category structure, no fiber functor, no
   curve pi_1 and no curve-to-anabelioid functor.  The tree concrete strips use
   the identity projection and are proved to have trivial geometric kernel
   (localDPrimeStrip_geometric_eq_bot); they are excluded here by
   no_fPsi_equiv_localOFieldStrip.  The companion S2037 records the same
   missing datum as CurvePi1Family.
2. OUnitsMuActor (component (c)): the group-theoretic algorithm of Example
   1.8, (iii)--(iv) does not exist in the tree; S1967 proves that the S1487
   carrier has trivial units, and S1978 attaches the actual local O-times
   carrier but not the algorithm.
3. ThetaMonoidActual (component (b)): the cohomological Psi_cns of
   [AbsTopIII], Corollary 1.10, (b) and its identification with the actual
   local integral monoid are not constructed; S1973 builds only the local-field
   model.
4. OperationKummerEvaluation (component (e)): it consumes (b) and (c), so it is
   missing until they exist; the operation-level Kummer/evaluation on the
   actual local O-times / O-times-mu carrier is constructed at the reduced
   level in the companion S2034/S2045.

No True, PUnit, empty type, arbitrary inhabitant, sorry, axiom or
assumption-only Nonempty gate is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S2038PaperOActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual (PaperV)
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open AlgebraicGeometry

variable {l : PrimeGeFive}

instance primeGeFiveFact (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

instance paperVFact (v : PaperV) : Fact (Nat.Prime v.1) :=
  ⟨v.prime⟩

/-! ## 1. The q-pilot generator: the actual local q-parameter -/

/-- The actual local q-parameter q = l of the paper bad place, as an element of
the actual local field Q_l.  This is the Tate parameter of
ConcreteTateParameter.canonical, not a realified value. -/
noncomputable def qPilotValue (l : PrimeGeFive) : ℚ_[l.value] :=
  (ConcreteTateParameter.canonical l).q

theorem qPilotValue_eq_prime (l : PrimeGeFive) :
    qPilotValue l = (l.value : ℚ_[l.value]) :=
  ConcreteTateParameter.canonical_q l

theorem qPilotValue_ne_zero (l : PrimeGeFive) : qPilotValue l ≠ 0 := by
  rw [qPilotValue_eq_prime]
  exact_mod_cast l.prime.ne_zero

theorem qPilotValue_ne_one (l : PrimeGeFive) : qPilotValue l ≠ 1 :=
  ConcreteTateParameter.canonical_q_ne_one l

/-- The actual O-triangle monoid of the q-pilot: the submonoid of the actual
local field generated by the actual q-parameter.  IUT II, Definition 4.9,
(viii): each O-triangle(-) is abstractly isomorphic to N, generated by the
q-parameter. -/
noncomputable def qPilotODaggerCarrier (l : PrimeGeFive) : Submonoid ℚ_[l.value] :=
  Submonoid.powers (qPilotValue l)

/-- The generator of O-triangle: the actual q-parameter itself. -/
noncomputable def qPilotODaggerGenerator (l : PrimeGeFive) : qPilotODaggerCarrier l :=
  ⟨qPilotValue l, Submonoid.mem_powers _⟩

theorem qPilotODaggerGenerator_coe (l : PrimeGeFive) :
    (qPilotODaggerGenerator l : ℚ_[l.value]) = qPilotValue l :=
  rfl

theorem qPilotODaggerGenerator_ne_one (l : PrimeGeFive) :
    qPilotODaggerGenerator l ≠ 1 := by
  intro h
  have h' : (qPilotODaggerGenerator l : ℚ_[l.value]) = 1 := by
    rw [h]
    simp
  rw [qPilotODaggerGenerator_coe] at h'
  exact qPilotValue_ne_one l h'

theorem qPilotODaggerCarrier_nontrivial (l : PrimeGeFive) :
    Nontrivial (qPilotODaggerCarrier l) :=
  ⟨⟨1, qPilotODaggerGenerator l, fun h => qPilotODaggerGenerator_ne_one l h.symm⟩⟩

/-- The actual q-parameter has infinite multiplicative order: no positive power
of it is 1. -/
theorem qPilotValue_pow_ne_one (l : PrimeGeFive) :
    ∀ n : ℕ, 0 < n → qPilotValue l ^ n ≠ 1 :=
  ConcreteTateParameter.q_power_ne_one l (ConcreteTateParameter.canonical l)

theorem qPilotValue_pow_injective (l : PrimeGeFive) :
    Function.Injective (fun m : ℕ => qPilotValue l ^ m) := by
  have key : ∀ a b : ℕ, a ≤ b → qPilotValue l ^ a = qPilotValue l ^ b → a = b := by
    intro a b hab hab_eq
    have h2 : qPilotValue l ^ a = qPilotValue l ^ a * qPilotValue l ^ (b - a) := by
      rw [← pow_add, Nat.add_sub_cancel' hab, hab_eq]
    have h3 : qPilotValue l ^ a * 1 = qPilotValue l ^ a * qPilotValue l ^ (b - a) := by
      rw [mul_one]
      exact h2
    have h4 : (1 : ℚ_[l.value]) = qPilotValue l ^ (b - a) :=
      mul_left_cancel₀ (pow_ne_zero a (qPilotValue_ne_zero l)) h3
    rcases Nat.eq_or_lt_of_le hab with hEq | hLt
    · exact hEq
    · exact absurd h4.symm (qPilotValue_pow_ne_one l (b - a) (Nat.sub_pos_of_lt hLt))
  intro m n h
  rcases Nat.le_total m n with hle | hle
  · exact key m n hle h
  · exact (key n m hle h.symm).symm

/-- O-triangle is abstractly isomorphic to N, as the paper states for each
O-triangle(-). -/
noncomputable def qPilotODaggerEquivNat (l : PrimeGeFive) :
    Multiplicative ℕ ≃* qPilotODaggerCarrier l := by
  classical
  exact Submonoid.powLogEquiv (qPilotValue_pow_injective l)

/-! ### The S1487 degenerate value monoid cannot carry the generator -/

/-- The degenerate S1487 value monoid is divisible: every element is a
square. -/
theorem sourceHaar_divisible (x : SourceHaarActualValueMonoid) :
    ∃ y : SourceHaarActualValueMonoid, y * y = x := by
  obtain ⟨a, ha⟩ :
      ∃ a : sourceHaarActualNonpositiveAddSubmonoid, Multiplicative.ofAdd a = x :=
    ⟨Multiplicative.toAdd x, rfl⟩
  have ha' : (a : ℝ) ≤ 0 := a.2
  refine ⟨Multiplicative.ofAdd ⟨(a : ℝ) / 2, ?_⟩, ?_⟩
  · exact div_nonpos_of_nonpos_of_nonneg ha' (by norm_num)
  · rw [← ha]
    show Multiplicative.ofAdd (⟨(a : ℝ) / 2, _⟩ + ⟨(a : ℝ) / 2, _⟩) =
      Multiplicative.ofAdd a
    congr 1
    apply Subtype.ext
    simp

/-- N is not divisible: ofAdd 1 has no square root. -/
theorem nat_no_sqrt_one :
    ¬ ∃ a : Multiplicative ℕ, a * a = Multiplicative.ofAdd 1 := by
  rintro ⟨a, ha⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a = Multiplicative.ofAdd n := ⟨a.toAdd, rfl⟩
  rw [hn] at ha
  have h2 : n + n = 1 := by
    have := congrArg Multiplicative.toAdd ha
    simpa using this
  omega

theorem qPilotODagger_no_sqrt_generator (l : PrimeGeFive) :
    ¬ ∃ a : qPilotODaggerCarrier l, a * a = qPilotODaggerGenerator l := by
  rintro ⟨a, ha⟩
  obtain ⟨n, hn⟩ :=
    (Submonoid.mem_powers_iff (a : ℚ_[l.value]) (qPilotValue l)).mp a.2
  have hv : (a : ℚ_[l.value]) * (a : ℚ_[l.value]) = qPilotValue l := by
    have h := congrArg (fun x : qPilotODaggerCarrier l => (x : ℚ_[l.value])) ha
    simpa [qPilotODaggerGenerator] using h
  rw [← hn] at hv
  have h2 : qPilotValue l ^ (n + n) = qPilotValue l := by
    rw [pow_add]
    exact hv
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have h2' : qPilotValue l = 1 := by simpa using h2.symm
    exact qPilotValue_ne_one l h2'
  · have h4 : qPilotValue l ^ (n + n) =
        qPilotValue l ^ (n + n - 1) * qPilotValue l := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h4] at h2
    have h5 : qPilotValue l ^ (n + n - 1) = 1 :=
      mul_right_cancel₀ (qPilotValue_ne_zero l) (h2.trans (one_mul _).symm)
    exact qPilotValue_pow_ne_one l (n + n - 1) (by omega) h5

/-- The actual q-pilot O-triangle carrier is not isomorphic to the degenerate
S1487 value monoid SourceHaarActualValueMonoid: the latter is divisible, the
former is N. -/
theorem qPilotODaggerCarrier_no_equiv_sourceHaar (l : PrimeGeFive) :
    ¬ Nonempty (qPilotODaggerCarrier l ≃* SourceHaarActualValueMonoid) := by
  rintro ⟨e⟩
  obtain ⟨y, hy⟩ := sourceHaar_divisible (e (qPilotODaggerGenerator l))
  obtain ⟨a, rfl⟩ := e.surjective y
  have haa : a * a = qPilotODaggerGenerator l := by
    apply e.injective
    rw [map_mul, hy]
  exact qPilotODagger_no_sqrt_generator l ⟨a, haa⟩

/-- The actual q-parameter is a non-unit integral element: its norm is less
than one. -/
theorem qPilotValue_norm_lt_one (l : PrimeGeFive) : ‖qPilotValue l‖ < 1 :=
  (ConcreteTateParameter.canonical l).q_norm_lt_one

/-- The constructed O-triangle carrier lies in the actual integral monoid of the
local field: every element has norm at most one.  This is the source condition
q_v in O-triangle of IUT I, Section 3. -/
theorem qPilotODagger_integral (l : PrimeGeFive) (x : qPilotODaggerCarrier l) :
    ‖(x : ℚ_[l.value])‖ ≤ 1 := by
  obtain ⟨n, hn⟩ :=
    (Submonoid.mem_powers_iff (x : ℚ_[l.value]) (qPilotValue l)).mp x.2
  rw [← hn, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (le_of_lt (qPilotValue_norm_lt_one l))

/-- The constructed actual q-pilot O-triangle datum (paper component (d)). -/
structure QPilotODaggerData (l : PrimeGeFive) where
  generator : qPilotODaggerCarrier l
  generator_is_q : (generator : ℚ_[l.value]) = qPilotValue l
  generator_ne_one : generator ≠ 1
  free : Multiplicative ℕ ≃* qPilotODaggerCarrier l
  infinite_order : Function.Injective (fun m : ℕ => generator ^ m)
  integral : ∀ x : qPilotODaggerCarrier l, ‖(x : ℚ_[l.value])‖ ≤ 1
  not_sourceHaar : ¬ Nonempty (qPilotODaggerCarrier l ≃* SourceHaarActualValueMonoid)

/-- The actual q-pilot O-triangle datum of the paper O object. -/
noncomputable def paperQPilotODaggerData (l : PrimeGeFive) : QPilotODaggerData l where
  generator := qPilotODaggerGenerator l
  generator_is_q := rfl
  generator_ne_one := qPilotODaggerGenerator_ne_one l
  free := qPilotODaggerEquivNat l
  infinite_order := by
    intro m n h
    have h' : (qPilotODaggerGenerator l : ℚ_[l.value]) ^ m =
        (qPilotODaggerGenerator l : ℚ_[l.value]) ^ n := by
      simpa using congrArg (fun x : qPilotODaggerCarrier l => (x : ℚ_[l.value])) h
    rw [qPilotODaggerGenerator_coe] at h'
    exact qPilotValue_pow_injective l h'
  integral := qPilotODagger_integral l
  not_sourceHaar := qPilotODaggerCarrier_no_equiv_sourceHaar l

theorem paperQPilotODaggerData_nonempty (l : PrimeGeFive) :
    Nonempty (QPilotODaggerData l) :=
  ⟨paperQPilotODaggerData l⟩


/-! ## 2. Component (a): the actual F-double-plus-prime-strip -/

/-- The actual tempered and etale fundamental-group data of the once-punctured
elliptic curve at a place, as required by IUT II, Definition 1.1 and
Example 1.8.  The curve is the actual affine curve curveScheme Q_v, card is the
certified etale fundamental group of its finite etale covers (the frozen source
card CurveEtaleFundamentalGroupCard), tempered is the tempered fundamental
group, and the projection onto the actual local absolute Galois group has
nontrivial geometric kernel. -/
structure CurvePiOneData (v : PaperV) where
  curve : Scheme
  curve_eq : curve = curveScheme ℚ_[v.1]
  card : CurveEtaleFundamentalGroupCard ℚ_[v.1]
  tempered : Type
  [groupTempered : Group tempered]
  [topTempered : TopologicalSpace tempered]
  comparison : tempered →* (card.fundamentalGroup : Type)
  proj : tempered →* @LocalAbsoluteGalois v.1 ⟨v.prime⟩
  proj_surjective : Function.Surjective proj
  geometric_nontrivial : Nontrivial proj.ker

/-- (a) The paper actual F-double-plus-prime-strip: the local O-times monoids of
the actual local fields, the actual once-punctured elliptic curves with their
tempered/etale fundamental groups, and the functorial surjections with
nontrivial geometric kernels. -/
structure FPsiPrimeStrip (l : PrimeGeFive) where
  strip : FPrimeStrip PaperV
  mon_equiv : ∀ v : PaperV, strip.Mon v ≃* LocalOFieldUnitsAt v
  g_eq : ∀ v : PaperV, strip.G v = @LocalAbsoluteGalois v.1 ⟨v.prime⟩
  piOne : (v : PaperV) → CurvePiOneData v
  pi_eq : ∀ v : PaperV, strip.Pi v = (piOne v).tempered
  geometric_nontrivial :
    ∀ v : PaperV, Nontrivial (DPrimeStrip.geometric strip.toDPrimeStrip v)

/-- Every subgroup with a nontrivial carrier is a nontrivial subgroup. -/
theorem ne_bot_of_nontrivial {G : Type*} [Group G] {H : Subgroup G}
    (h : Nontrivial H) : H ≠ ⊥ := by
  intro hbot
  obtain ⟨x, y, hxy⟩ := h.exists_pair_ne
  apply hxy
  apply Subtype.ext
  have hx : (x : G) ∈ (⊥ : Subgroup G) := by
    rw [← hbot]
    exact x.2
  have hy : (y : G) ∈ (⊥ : Subgroup G) := by
    rw [← hbot]
    exact y.2
  rw [Subgroup.mem_bot] at hx hy
  rw [hx, hy]

/-- The reduced identity-projection local strip has trivial geometric kernel:
its projection is the identity. -/
theorem localOFieldStrip_geometric_bot (v : PaperV) :
    DPrimeStrip.geometric localOFieldStrip.toDPrimeStrip v = ⊥ := by
  show (localOFieldStrip.toDPrimeStrip.proj v).ker = ⊥
  rw [show localOFieldStrip.toDPrimeStrip.proj v = MonoidHom.id _ from rfl]
  exact MonoidHom.ker_id

/-- The paper F-double-plus-prime-strip has nontrivial geometric kernel at
every place. -/
theorem fPsi_geometric_ne_bot (F : FPsiPrimeStrip l) (v : PaperV) :
    DPrimeStrip.geometric F.strip.toDPrimeStrip v ≠ ⊥ :=
  ne_bot_of_nontrivial (F.geometric_nontrivial v)

/-- The reduced strip is excluded.  No F-double-plus-prime-strip of the paper is
equivalent, as an F-prime-strip, to the identity-projection reduced strip
localOFieldStrip: strip equivalence would transfer triviality of the geometric
kernel, but the paper kernel is nontrivial. -/
theorem no_fPsi_equiv_localOFieldStrip (F : FPsiPrimeStrip l) (v : PaperV) :
    ¬ Nonempty (FPrimeStripEquiv F.strip localOFieldStrip) := by
  rintro ⟨phi⟩
  have hbot : ∀ w : PaperV,
      DPrimeStrip.geometric localOFieldStrip.toDPrimeStrip w = ⊥ :=
    fun w => localOFieldStrip_geometric_bot w
  exact fPsi_geometric_ne_bot F v
    (geometric_eq_bot_of_stripEquiv phi.symm.toD hbot v)

/-- The degenerate S1487 monoid is excluded from (a).  The local monoids of the
paper F-double-plus-prime-strip cannot be identified with the unit group of the
degenerate S1487 value monoid. -/
theorem fPsi_mon_not_sourceHaar (F : FPsiPrimeStrip l) (v : PaperV) :
    ¬ Nonempty (F.strip.Mon v ≃* SourceHaarActualValueMonoidˣ) := by
  rintro ⟨e⟩
  exact @no_localOFieldUnits_equiv_sourceHaarUnits v.1 ⟨v.prime⟩
    ⟨(F.mon_equiv v).symm.trans e⟩

/-- The first link of the missing chain: the curve pi_1 datum at every place. -/
theorem fPsi_curvePiOne (F : FPsiPrimeStrip l) (v : PaperV) :
    Nonempty (CurvePiOneData v) :=
  ⟨F.piOne v⟩

/-! ## 3. Component (b): the paper-level theta and Gaussian monoid -/

/-- (b) The paper-level theta and Gaussian monoid assignment Psi_env, Psi_gau of
IUT II, Corollary 4.6, (iv), on the actual F-double-plus-prime-strip and the
fixed finite theta packet of the actual input.  The theta values are the
Gaussian special values of the actual packet, and the evaluation is the
Gaussian evaluation of Proposition 4.1, (iv). -/
structure ThetaMonoidActual (I : Theorem311Source.OriginalInput l PaperV)
    (F : FPsiPrimeStrip l) where
  env : PaperV → Type
  gau : PaperV → Type
  [commMonoidEnv : ∀ v, CommMonoid (env v)]
  [commMonoidGau : ∀ v, CommMonoid (gau v)]
  thetaValue : (v : PaperV) → SignedLabel l.value → env v
  qElement : (v : PaperV) → env v
  thetaValue_eq : ∀ v (j : SignedLabel l.value),
    thetaValue v j = qElement v ^ (gaussExponent j.1).toNat
  evaluation : (v : PaperV) → env v →* gau v
  evaluation_bijective : ∀ v, Function.Bijective (evaluation v)
  valueMap : (v : PaperV) → env v →* NNReal
  value_theta : ∀ v (j : SignedLabel l.value),
    valueMap v (thetaValue v j) = Real.toNNReal ((I.theaterAt 0 0).thetaPacket.scale j)
  value_q : ∀ v,
    valueMap v (qElement v) = Real.toNNReal ((I.theaterAt 0 0).thetaPacket.q)

/-! ## 4. Component (c): the group-theoretic O-times-mu(G) actor -/

/-- (c) The group-theoretic actor O-times-mu(G) of IUT II, Example 1.8,
(iii)--(iv).  alg is the construction from a profinite group G alone, algMap
its functoriality under isomorphisms of profinite groups, and the actor at each
place is alg evaluated at the actual local absolute Galois group, identified
with the actual local O-times-mu. -/
structure OUnitsMuActor (l : PrimeGeFive) (F : FPsiPrimeStrip l) where
  alg : ProfiniteGrp → Type
  [commMonoidAlg : ∀ G : ProfiniteGrp, CommMonoid (alg G)]
  algMap : ∀ {G H : ProfiniteGrp}, G ≃* H → alg G ≃* alg H
  actor : PaperV → Type
  [commMonoidActor : ∀ v, CommMonoid (actor v)]
  actor_eq : ∀ v, actor v = alg (@localAbsoluteGaloisProfinite v.1 ⟨v.prime⟩)
  actor_equiv_local : ∀ v, Nonempty (actor v ≃* LocalOFieldUnitsMuAt v)
  action : ∀ v, @LocalAbsoluteGalois v.1 ⟨v.prime⟩ →* MulAut (actor v)

/-! ## 5. Component (e): the operation-level Kummer and evaluation -/

/-- (e) The operation-level Kummer isomorphism (IUT II, Definition 4.9, (i)) and
evaluation isomorphism (IUT II, Corollary 4.10, (ii)) between the
group-theoretic side O-times-mu(G_v) and the Frobenioid side O-times-mu of the
actual local monoid, together with the Gaussian evaluation on the theta
monoid. -/
structure OperationKummerEvaluation (I : Theorem311Source.OriginalInput l PaperV)
    (F : FPsiPrimeStrip l) (theta : ThetaMonoidActual I F)
    (A : OUnitsMuActor l F) (q : QPilotODaggerData l) where
  groupSide : PaperV → Type
  [commMonoidGroupSide : ∀ v, CommMonoid (groupSide v)]
  frobSide : PaperV → Type
  [commMonoidFrobSide : ∀ v, CommMonoid (frobSide v)]
  groupSide_eq : ∀ v, groupSide v = A.actor v
  frobSide_eq : ∀ v, frobSide v = LocalOFieldUnitsMuAt v
  kummer : ∀ v, groupSide v ≃* frobSide v
  evalSource : PaperV → Type
  [commMonoidEvalSource : ∀ v, CommMonoid (evalSource v)]
  evalTarget : PaperV → Type
  [commMonoidEvalTarget : ∀ v, CommMonoid (evalTarget v)]
  evalSource_eq : ∀ v, evalSource v = theta.env v
  evalTarget_eq : ∀ v, evalTarget v = theta.gau v
  evaluation : ∀ v, evalSource v ≃* evalTarget v

/-! ## 6. The paper O object and its exact first-missing chain -/

/-- The paper actual O object.  Its five components are exactly the components
of IUT II, Definitions 1.1 and 4.9, Example 1.8, and Corollary 4.10, (ii):
(a) the actual F-double-plus-prime-strip, (b) the paper-level theta/Gaussian
monoid, (c) the group-theoretic O-times-mu(G) actor, (d) the actual q-pilot
O-triangle generator, and (e) the operation-level Kummer/evaluation. -/
structure PaperOActual (I : Theorem311Source.OriginalInput l PaperV) where
  fStackPlus : FPsiPrimeStrip l
  theta : ThetaMonoidActual I fStackPlus
  oUnitsMu : OUnitsMuActor l fStackPlus
  qPilot_generator : (paperQPilotODaggerData l).generator = qPilotODaggerGenerator l
  qPilot_not_sourceHaar :
    ¬ Nonempty (qPilotODaggerCarrier l ≃* SourceHaarActualValueMonoid)
  kummer : OperationKummerEvaluation I fStackPlus theta oUnitsMu
    (paperQPilotODaggerData l)

/-- The exact first-missing bundle of the paper O object: components (a), (b),
(c), (e), with the constructed q-pilot (d) already fixed. -/
structure PaperOFirstMissing (I : Theorem311Source.OriginalInput l PaperV) where
  fStackPlus : FPsiPrimeStrip l
  theta : ThetaMonoidActual I fStackPlus
  oUnitsMu : OUnitsMuActor l fStackPlus
  kummer : OperationKummerEvaluation I fStackPlus theta oUnitsMu
    (paperQPilotODaggerData l)

/-- The first-missing bundle of a paper O object. -/
def paperOFirstMissing_of_actual {l : PrimeGeFive}
    {I : Theorem311Source.OriginalInput l PaperV}
    (X : PaperOActual I) : PaperOFirstMissing I where
  fStackPlus := X.fStackPlus
  theta := X.theta
  oUnitsMu := X.oUnitsMu
  kummer := X.kummer

/-- A paper O object from its first-missing bundle and the constructed
q-pilot. -/
def paperOActual_of_firstMissing {l : PrimeGeFive}
    {I : Theorem311Source.OriginalInput l PaperV}
    (M : PaperOFirstMissing I) : PaperOActual I where
  fStackPlus := M.fStackPlus
  theta := M.theta
  oUnitsMu := M.oUnitsMu
  qPilot_generator := rfl
  qPilot_not_sourceHaar := qPilotODaggerCarrier_no_equiv_sourceHaar l
  kummer := M.kummer

/-- The paper O object is nonempty exactly when its first-missing bundle is.
The q-pilot component (d) is constructed outright; the remaining four
components are the exact first missing. -/
theorem nonempty_paperOActual_iff (I : Theorem311Source.OriginalInput l PaperV) :
    Nonempty (PaperOActual I) ↔ Nonempty (PaperOFirstMissing I) := by
  constructor
  · rintro ⟨X⟩
    exact ⟨paperOFirstMissing_of_actual X⟩
  · rintro ⟨M⟩
    exact ⟨paperOActual_of_firstMissing M⟩

/-- The first link of the missing chain, restated for the first-missing bundle:
an actual curve pi_1 datum at every place. -/
theorem firstMissing_curvePiOne (M : PaperOFirstMissing I) (v : PaperV) :
    Nonempty (CurvePiOneData v) :=
  fPsi_curvePiOne M.fStackPlus v

/-- The first missing bundle excludes the reduced identity-projection strip. -/
theorem firstMissing_excludes_reduced (M : PaperOFirstMissing I) (v : PaperV) :
    ¬ Nonempty (FPrimeStripEquiv M.fStackPlus.strip localOFieldStrip) :=
  no_fPsi_equiv_localOFieldStrip M.fStackPlus v

/-- The paper O object has the actual local O-times monoids, not the degenerate
S1487 monoid. -/
theorem paperOActual_mon_not_sourceHaar (X : PaperOActual I) (v : PaperV) :
    ¬ Nonempty (X.fStackPlus.strip.Mon v ≃* SourceHaarActualValueMonoidˣ) :=
  fPsi_mon_not_sourceHaar X.fStackPlus v

/-- The paper O object q-pilot generator is the actual q = l and its carrier is
not the degenerate S1487 value monoid. -/
theorem paperOActual_qPilot_actual {l : PrimeGeFive}
    {I : Theorem311Source.OriginalInput l PaperV} (X : PaperOActual I) :
    ((paperQPilotODaggerData l).generator : ℚ_[l.value]) = qPilotValue l ∧
      ¬ Nonempty (qPilotODaggerCarrier l ≃* SourceHaarActualValueMonoid) :=
  ⟨rfl, X.qPilot_not_sourceHaar⟩

/-! ## 7. Axiom probes -/

#print axioms qPilotODaggerCarrier_no_equiv_sourceHaar
#print axioms qPilotValue_pow_injective
#print axioms paperQPilotODaggerData
#print axioms no_fPsi_equiv_localOFieldStrip
#print axioms fPsi_mon_not_sourceHaar
#print axioms nonempty_paperOActual_iff
#print axioms paperOActual_qPilot_actual

end LeanFormal.IUT.XiFPaper.S2038PaperOActual

