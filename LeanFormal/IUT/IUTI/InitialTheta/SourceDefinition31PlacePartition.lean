import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31RootLemmas
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceSelection
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# IUT I Definition 3.1(a)(b): the source place partition, D3 entry layer

Consumers: `IUT-I.definition-3.1-D11-E-construction` (the clauses (a)-(f)
assembly of `SourceDefinition31RootLemmas.lean`) and the `initialThetaData`
source side of the Theorem 3.11 input chain (items 22-31). This module is the
D3 entry point of the Definition 3.1 construction chain: it names the
conditional assembly of the place partition from `InitialThetaArithmeticData`
plus two explicitly supplied source inputs.

The two source inputs are hypotheses; they are never manufactured here:

* `SourcePlaceSelection A` - the bad moduli set V^bad_mod of Definition
  3.1(b): finite places of `A.Fmod` with odd residue characteristic, with
  nonemptiness;
* `Fintype (Bad P)` - the finiteness of V^bad_mod.

The open obligation is recorded in the audit as
`IUT-I.definition-3.1-D3-arithmetic-bad-moduli-gap`: deriving the bad-moduli
locus from the curve's reduction needs a base-change bridge from
`A.curve : PuncturedEllipticCurve A.F` to places of `A.Fmod`, fibre-uniformity
of the reduction type, finiteness from the discriminant support, and the
oddness/nonemptiness source conditions. The D3 gate `D3PlaceConstruction` is
not closed, and no degenerate selection is used to close it.

Paper anchors: IUT I, Definition 3.1(a) (place partition V(F) = V_non ⊔
V_arc), (b) (bad moduli set and residue characteristics), (e) (bijection
V_mod ≃ V(F)); Sections 3-4.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT

universe u

noncomputable section

namespace InitialThetaSource

namespace Definition31PlacePartition

open PlacePartitionReduction

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}

/-- The D3 assembly handle: the source place partition of a supplied bad
moduli selection with a finite bad index. Definitionally the reduction-module
assembly `toSourcePlacePartition`. -/
def d3PlacePartition (P : SourcePlaceSelection A) [Fintype (Bad P)] :
    Theorem311Source.SourcePlacePartition (Selected P) (Bad P) :=
  toSourcePlacePartition P

@[simp] theorem d3PlacePartition_eq (P : SourcePlaceSelection A)
    [Fintype (Bad P)] :
    d3PlacePartition P = toSourcePlacePartition P :=
  rfl

/-- D3 gate body with supplied inputs: from the arithmetic input and the two
source inputs the place partition exists. This is the supplied-input form of
`SourceDefinition31Root.D3PlaceConstruction`; the gate itself remains open. -/
theorem placeConstruction_of_selection (P : SourcePlaceSelection A)
    [Finite (Bad P)] :
    ∃ (Selected Bad : Type u),
      Nonempty (Theorem311Source.SourcePlacePartition Selected Bad) := by
  haveI : Fintype (Bad P) := Fintype.ofFinite (Bad P)
  exact ⟨Selected P, Bad P, ⟨d3PlacePartition P⟩⟩

/-- The D3 specification bundle: the constructed partition has nonempty
selected places, the Clause (e) finite-index bijection with cover and
disjointness, restriction compatibility, and the Clause (b) label
compatibility. -/
theorem partition_spec (P : SourcePlaceSelection A) [Fintype (Bad P)] :
    Nonempty (Selected P) ∧
      Function.Bijective (kindEquiv P) ∧
      (∀ w : Selected P,
        (∃ p : NumberField.FinitePlace A.Fmod, finiteToV P p = w) ∨
          (∃ s : NumberField.InfinitePlace A.Fmod,
            infiniteToV P s = w)) ∧
      Disjoint (Set.range (finiteToV P)) (Set.range (infiniteToV P)) ∧
      (∀ p : NumberField.FinitePlace A.Fmod,
        NumberFieldPlace.comap (k := A.Fmod) (finiteToV P p).1 =
          NumberFieldPlace.finite p) ∧
      (∀ b : Bad P,
        (d3PlacePartition P).selectedLabel
            ((d3PlacePartition P).badIncluded b) =
          (d3PlacePartition P).badLabel b) := by
  refine ⟨selectedNonempty P, kindEquiv_bijective P, selected_kind_cover P,
    finiteToV_range_disjoint P, finiteToV_comap P, ?_⟩
  intro b
  rw [d3PlacePartition_eq]
  exact (toSourcePlacePartition P).badLabel_compatible b

/-- The Clause (b) bad labels of the D3 partition are prime and odd. -/
theorem d3PlacePartition_badLabel_prime_odd (P : SourcePlaceSelection A)
    [Fintype (Bad P)] (b : Bad P) :
    Nat.Prime ((d3PlacePartition P).badLabel b) ∧
      Odd ((d3PlacePartition P).badLabel b) := by
  rw [d3PlacePartition_eq, toSourcePlacePartition_badLabel]
  exact ⟨badResidueLabel_prime P b, badResidueLabel_odd P b⟩

end Definition31PlacePartition

end InitialThetaSource

namespace Audit

def sourceDefinition31PlacePartitionAssembly : Obligation :=
  { id := "IUT-I.definition-3.1-D3-conditional-assembly"
    source := "IUT I, Definition 3.1(a)(b)(e); Sections 3-4"
    status := VerificationStatus.conditional
    note :=
      "With InitialThetaArithmeticData, a supplied source selection " ++
        "(bad moduli set with odd residue characteristic and nonemptiness), " ++
        "and finiteness of the bad moduli index, " ++
        "`Definition31PlacePartition.placeConstruction_of_selection` yields " ++
        "a value of the D3 gate body, `d3PlacePartition` names the assembly, " ++
        "and `partition_spec` records the Clause (e) bijection, cover, " ++
        "disjointness, and restriction compatibility plus the Clause (b) " ++
        "label compatibility; `d3PlacePartition_badLabel_prime_odd` records " ++
        "primality and oddness of the labels. The two source inputs remain " ++
        "hypotheses; the D3 gate D3PlaceConstruction is not closed. " ++
        "Consumers: IUT-I.definition-3.1-D11-E-construction and the " ++
        "Theorem 3.11 input chain (items 22-31)."
    dependsOn :=
      [ "IUT-I.definition-3.1-D2-arithmetic-root",
        "IUT-I.definition-3.1-D3-place-partition" ] }

def sourceDefinition31BadModuliGap : Obligation :=
  { id := "IUT-I.definition-3.1-D3-arithmetic-bad-moduli-gap"
    source := "IUT I, Definition 3.1(a)(b); Sections 3-4 reduction input"
    status := VerificationStatus.pending
    note :=
      "Object: the curve-derived bad-moduli locus over A.Fmod - a finite " ++
        "nonempty set of finite places with odd residue characteristic (the " ++
        "source V^bad_mod), i.e. a SourcePlaceSelection together with " ++
        "finiteness of its bad subtype, derived from A.curve. Quantifier: " ++
        "for every A : InitialThetaArithmeticData l, without further " ++
        "hypotheses. Missing sub-gaps: (i) a base-change bridge from " ++
        "A.curve over A.F to reduction at places of A.Fmod, with " ++
        "fibre-uniformity of the reduction type (HasGoodReductionAt is " ++
        "stated only over A.F); (ii) finiteness from the discriminant " ++
        "support (currently an explicit Fintype hypothesis); (iii) oddness " ++
        "of the residue characteristics (source condition; characteristic 2 " ++
        "is not excluded by the interface); (iv) nonemptiness (source " ++
        "condition). Failed routes: a singleton or otherwise degenerate bad " ++
        "set satisfies the literal D3 gate body but is not the source " ++
        "partition, rejected; badness defined from a chosen lift without " ++
        "uniformity is choice-dependent, rejected; legacy modules " ++
        "(SourceDefinition31D3D4Root.lean and siblings) have no compiled " ++
        "olean and are not usable. The gate D3PlaceConstruction stays open."
    dependsOn :=
      [ "IUT-I.definition-3.1-D3-conditional-assembly",
        "IUT-I.initial-theta-reduction-place-partition" ] }

end Audit

namespace InitialThetaSource

namespace Definition31PlacePartition

open PlacePartitionReduction

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}

/-- D11-E construction entry handle: assembles `SourceDefinition31Data` from
the arithmetic input, the supplied source selection with finite bad index,
the bad-place reduction cards, the four clause inputs, and the five
arithmetic-compatibility propositions with their proofs (each supplied as an
explicit hypothesis). The reduction component is the reduction-module
assembly `toSourceReductionClause`; no field is manufactured. -/
noncomputable def d11EntryData (P : SourcePlaceSelection A) [Fintype (Bad P)]
    (C : BadPlaceReductionCards P)
    (T : Theorem311Source.SourceTorsionClause l)
    (O : Theorem311Source.SourceOrbicurveClause)
    (Se : Theorem311Source.SourceSectionClause)
    (Cu : Theorem311Source.SourceCuspClause)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    Theorem311Source.SourceDefinition31Data l :=
  { arithmetic := A
    selectedPlaces := Selected P
    badPlaces := Bad P
    reduction := toSourceReductionClause P C
    torsion := T
    orbicurve := O
    sections := Se
    cusp := Cu
    arithmetic_reduction_compatibility := redCompat
    arithmetic_reduction_compatibility_proved := hredCompat
    arithmetic_torsion_compatibility := torCompat
    arithmetic_torsion_compatibility_proved := htorCompat
    arithmetic_orbicurve_compatibility := orbCompat
    arithmetic_orbicurve_compatibility_proved := horbCompat
    arithmetic_section_compatibility := secCompat
    arithmetic_section_compatibility_proved := hsecCompat
    arithmetic_cusp_compatibility := cusCompat
    arithmetic_cusp_compatibility_proved := hcusCompat }

/-- The reduction component of `d11EntryData` is the reduction-module
assembly `toSourceReductionClause`. -/
theorem d11EntryData_reduction (P : SourcePlaceSelection A) [Fintype (Bad P)]
    (C : BadPlaceReductionCards P)
    (T : Theorem311Source.SourceTorsionClause l)
    (O : Theorem311Source.SourceOrbicurveClause)
    (Se : Theorem311Source.SourceSectionClause)
    (Cu : Theorem311Source.SourceCuspClause)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (d11EntryData P C T O Se Cu redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).reduction =
      toSourceReductionClause P C := rfl

/-- The torsion component of `d11EntryData` is the supplied torsion clause. -/
theorem d11EntryData_torsion (P : SourcePlaceSelection A) [Fintype (Bad P)]
    (C : BadPlaceReductionCards P)
    (T : Theorem311Source.SourceTorsionClause l)
    (O : Theorem311Source.SourceOrbicurveClause)
    (Se : Theorem311Source.SourceSectionClause)
    (Cu : Theorem311Source.SourceCuspClause)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (d11EntryData P C T O Se Cu redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).torsion =
      T := rfl

end Definition31PlacePartition

namespace Definition31BadReductionFiniteness

open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped WithZero

variable {F : Type*} [Field F] [NumberField F]

/-- Route-4 candidate bad support: the finite union of the discriminant
support, the inverse-discriminant support, and the supports of `a1, a2, a3,
a4, a6` over the ring of integers of `F`. -/
noncomputable def candidateBadSupport (W : WeierstrassCurve F) :
    Set (HeightOneSpectrum (NumberField.RingOfIntegers F)) :=
  Support (NumberField.RingOfIntegers F) W.Δ ∪
  Support (NumberField.RingOfIntegers F) W.Δ⁻¹ ∪
  Support (NumberField.RingOfIntegers F) W.a₁ ∪
  Support (NumberField.RingOfIntegers F) W.a₂ ∪
  Support (NumberField.RingOfIntegers F) W.a₃ ∪
  Support (NumberField.RingOfIntegers F) W.a₄ ∪
  Support (NumberField.RingOfIntegers F) W.a₆

/-- The candidate bad support is finite, by the seven support finiteness
theorems of Mathlib. -/
theorem candidateBadSupport_finite (W : WeierstrassCurve F) :
    (candidateBadSupport W).Finite := by
  unfold candidateBadSupport
  exact ((((((Support.finite (NumberField.RingOfIntegers F) W.Δ).union
    (Support.finite (NumberField.RingOfIntegers F) W.Δ⁻¹)).union
    (Support.finite (NumberField.RingOfIntegers F) W.a₁)).union
    (Support.finite (NumberField.RingOfIntegers F) W.a₂)).union
    (Support.finite (NumberField.RingOfIntegers F) W.a₃)).union
    (Support.finite (NumberField.RingOfIntegers F) W.a₄)).union
    (Support.finite (NumberField.RingOfIntegers F) W.a₆)

/-- Outside the candidate bad support all seven quantities above are
integral at the place: each valuation is at most one. -/
theorem not_mem_candidateBadSupport_iff (W : WeierstrassCurve F)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    v ∉ candidateBadSupport W ↔
      (¬ 1 < v.valuation F W.Δ) ∧
      (¬ 1 < v.valuation F W.Δ⁻¹) ∧
      (¬ 1 < v.valuation F W.a₁) ∧
      (¬ 1 < v.valuation F W.a₂) ∧
      (¬ 1 < v.valuation F W.a₃) ∧
      (¬ 1 < v.valuation F W.a₄) ∧
      (¬ 1 < v.valuation F W.a₆) := by
  simp only [candidateBadSupport, Support, Set.mem_union, Set.mem_setOf_eq, not_or,
    and_assoc]

/-- In a linearly ordered commutative group with zero, a product one with
both factors at most one forces the first factor to be one. -/
theorem eq_one_of_le_one_of_mul_eq_one {M : Type*}
    [LinearOrderedCommGroupWithZero M] {a b : M}
    (h₁ : a ≤ 1) (h₂ : b ≤ 1) (hmul : a * b = 1) : a = 1 := by
  have hge : 1 ≤ a := by
    have h : a * b ≤ a := mul_le_of_le_one_right' h₂
    rwa [hmul] at h
  exact le_antisymm h₁ hge

/-- The underlying-prime map from finite places of `F` to height-one primes
of the ring of integers is injective. -/
theorem underlyingPrime_injective :
    Function.Injective (NumberFieldFinitePlace.underlyingPrime (K := F)) :=
  NumberField.FinitePlace.maximalIdeal_injective

/-- Route-4 bridge step (F level): if a finite place of `F` is outside the
candidate bad support, then the base-changed curve has good reduction there.
The proof shows the equation is integral with unit discriminant at the
completion, hence minimal with discriminant valuation one, hence has good
reduction. -/
theorem hasGoodReductionAt_of_notMem_candidateBadSupport
    (X : PuncturedEllipticCurve F) (p : NumberField.FinitePlace F)
    (hp : NumberFieldFinitePlace.underlyingPrime p ∉
      candidateBadSupport X.curve) :
    X.HasGoodReductionAt p := by
  obtain ⟨hΔ, hΔinv, ha₁, ha₂, ha₃, ha₄, ha₆⟩ :=
    (not_mem_candidateBadSupport_iff X.curve
      (NumberFieldFinitePlace.underlyingPrime p)).mp hp
  let W := X.curve
  let vv := NumberFieldFinitePlace.underlyingPrime p
  haveI hEll : W.IsElliptic := X.isElliptic
  have hΔ0 : W.Δ ≠ 0 := isUnit_iff_ne_zero.mp W.isUnit_Δ
  have hprod : vv.valuation F W.Δ * vv.valuation F W.Δ⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hΔ0, map_one]
  have hveq : vv.valuation F W.Δ = 1 :=
    eq_one_of_le_one_of_mul_eq_one (le_of_not_gt hΔ)
      (le_of_not_gt hΔinv) hprod
  have hvalued : Valued.v (W.baseChange (vv.adicCompletion F)).Δ = 1 := by
    have hΔeq : (W.baseChange (vv.adicCompletion F)).Δ =
        algebraMap F (vv.adicCompletion F) W.Δ := by
      rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
    rw [hΔeq]
    change Valued.v (W.Δ : vv.adicCompletion F) = 1
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hveq
  have hmem : ∀ c : F, ¬ 1 < vv.valuation F c →
      algebraMap F (vv.adicCompletion F) c ∈ vv.adicCompletionIntegers F :=
    fun c hc => by
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (c : vv.adicCompletion F) ≤ 1
      rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact le_of_not_gt hc
  have hInt : WeierstrassCurve.IsIntegral (vv.adicCompletionIntegers F)
      (W.baseChange (vv.adicCompletion F)) := by
    apply WeierstrassCurve.isIntegral_of_exists_lift
      (vv.adicCompletionIntegers F)
    · exact ⟨⟨algebraMap F (vv.adicCompletion F) W.a₁, hmem W.a₁ ha₁⟩, by
        rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
          ValuationSubring.algebraMap_apply]⟩
    · exact ⟨⟨algebraMap F (vv.adicCompletion F) W.a₂, hmem W.a₂ ha₂⟩, by
        rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₂,
          ValuationSubring.algebraMap_apply]⟩
    · exact ⟨⟨algebraMap F (vv.adicCompletion F) W.a₃, hmem W.a₃ ha₃⟩, by
        rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₃,
          ValuationSubring.algebraMap_apply]⟩
    · exact ⟨⟨algebraMap F (vv.adicCompletion F) W.a₄, hmem W.a₄ ha₄⟩, by
        rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₄,
          ValuationSubring.algebraMap_apply]⟩
    · exact ⟨⟨algebraMap F (vv.adicCompletion F) W.a₆, hmem W.a₆ ha₆⟩, by
        rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₆,
          ValuationSubring.algebraMap_apply]⟩
  have hval : (IsDiscreteValuationRing.maximalIdeal
      (vv.adicCompletionIntegers F)).valuation (vv.adicCompletion F)
        (W.baseChange (vv.adicCompletion F)).Δ = 1 := by
    have hmemd : (W.baseChange (vv.adicCompletion F)).Δ ∈
        vv.adicCompletionIntegers F := by
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      exact hvalued.le
    have hnotmem : (⟨(W.baseChange (vv.adicCompletion F)).Δ, hmemd⟩ :
        vv.adicCompletionIntegers F) ∉
        IsLocalRing.maximalIdeal (vv.adicCompletionIntegers F) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hunit
      exact hunit
        ((IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
          (v := vv)).mpr hvalued)
    change (IsDiscreteValuationRing.maximalIdeal
      (vv.adicCompletionIntegers F)).valuation (vv.adicCompletion F)
        (algebraMap (vv.adicCompletionIntegers F) (vv.adicCompletion F)
          (⟨(W.baseChange (vv.adicCompletion F)).Δ, hmemd⟩ :
            vv.adicCompletionIntegers F)) = 1
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem
      (v := IsDiscreteValuationRing.maximalIdeal (vv.adicCompletionIntegers F))
      (K := vv.adicCompletion F)
      (r := ⟨(W.baseChange (vv.adicCompletion F)).Δ, hmemd⟩)).mpr hnotmem
  haveI hIntI : WeierstrassCurve.IsIntegral (vv.adicCompletionIntegers F)
      (W.baseChange (vv.adicCompletion F)) := hInt
  haveI hMin : WeierstrassCurve.IsMinimal (vv.adicCompletionIntegers F)
      (W.baseChange (vv.adicCompletion F)) := by
    constructor
    constructor
    · simpa only [one_smul] using hInt
    · intro C hC _
      letI : WeierstrassCurve.IsIntegral (vv.adicCompletionIntegers F)
          (C • W.baseChange (vv.adicCompletion F)) := hC
      change (WeierstrassCurve.valuation_Δ_aux (vv.adicCompletionIntegers F)
          (C • W.baseChange (vv.adicCompletion F)) : ℤᵐ⁰) ≤
        (WeierstrassCurve.valuation_Δ_aux (vv.adicCompletionIntegers F)
          ((1 : WeierstrassCurve.VariableChange (vv.adicCompletion F)) •
            W.baseChange (vv.adicCompletion F)) : ℤᵐ⁰)
      have hbound := (WeierstrassCurve.valuation_Δ_aux
        (vv.adicCompletionIntegers F)
        (C • W.baseChange (vv.adicCompletion F))).property
      simpa only [one_smul, WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral,
        hval] using hbound
  have hgood : (W.baseChange (vv.adicCompletion F)).HasGoodReduction
      (vv.adicCompletionIntegers F) :=
    WeierstrassCurve.HasGoodReduction.mk hval
  change HasGoodReductionOnMinimalModel (vv.adicCompletionIntegers F)
    (W.baseChange (vv.adicCompletion F))
  exact ⟨1, by simpa only [one_smul] using hgood⟩

/-- Route-4 finiteness theorem (F level): there is a finite set of finite
places of `F` outside of which `X` has good reduction; the witness is the
finite candidate bad support of the discriminant and coefficients. -/
theorem exists_finite_goodReduction_off (X : PuncturedEllipticCurve F) :
    ∃ S : Set (NumberField.FinitePlace F), S.Finite ∧
      ∀ p : NumberField.FinitePlace F, p ∉ S → X.HasGoodReductionAt p := by
  refine ⟨{p | NumberFieldFinitePlace.underlyingPrime p ∈
    candidateBadSupport X.curve}, ?_, ?_⟩
  · have hinj : Set.InjOn (NumberFieldFinitePlace.underlyingPrime (K := F))
        (NumberFieldFinitePlace.underlyingPrime (K := F) ⁻¹'
          candidateBadSupport X.curve) :=
      fun _ _ _ _ h => underlyingPrime_injective h
    exact Set.Finite.preimage hinj (candidateBadSupport_finite X.curve)
  · intro p hp
    exact hasGoodReductionAt_of_notMem_candidateBadSupport X p hp

end Definition31BadReductionFiniteness

end InitialThetaSource

namespace Audit

def sourceDefinition31BadReductionFiniteness : Obligation :=
  { id := "IUT-I.definition-3.1-D3-bad-reduction-finiteness"
    source := "IUT I, Definition 3.1(b); Sections 3-4 reduction input"
    status := VerificationStatus.conditional
    note :=
      "Conditional finiteness side of the bad-moduli gap, closed at the " ++
        "level of the upper field F: the candidate bad support of the " ++
        "discriminant and coefficients is finite " ++
        "(`candidateBadSupport_finite`), off it the base-changed equation is " ++
        "integral with unit discriminant, hence minimal with discriminant " ++
        "valuation one, hence has good reduction " ++
        "(`hasGoodReductionAt_of_notMem_candidateBadSupport`), so a finite " ++
        "exceptional set with good reduction outside exists " ++
        "(`exists_finite_goodReduction_off`). Boundary: the F-to-Fmod " ++
        "base-change bridge with fibre-uniformity, oddness of residue " ++
        "characteristics, and nonemptiness remain source conditions; no " ++
        "`SourcePlaceSelection` is derived from the curve here, and the " ++
        "umbrella card `IUT-I.definition-3.1-D3-arithmetic-bad-moduli-gap` " ++
        "stays pending. Consumers: `IUT-I.definition-3.1-D3-arithmetic-bad-moduli-gap` " ++
        "and `IUT-I.definition-3.1-D11-E-construction`."
    dependsOn :=
      [ "IUT-I.definition-3.1-D3-arithmetic-bad-moduli-gap",
        "IUT-I.definition-3.1-D3-conditional-assembly" ] }

end Audit

end

end LeanFormal.IUT
