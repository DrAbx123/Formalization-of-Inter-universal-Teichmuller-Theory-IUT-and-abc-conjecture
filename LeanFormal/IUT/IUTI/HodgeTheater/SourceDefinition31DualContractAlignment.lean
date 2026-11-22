/-
  Alignment of the two in-repo contracts for IUT I Definition 3.1.

  Paper anchor (`D:\lean\papers\motizuki_corpus\text\Inter-universal
  Teichmuller Theory I.txt`, extraction lines normalized): Definition 3.1
  (line 3122) refers to as initial Theta-data any collection (F-bar/F, X_F,
  l, C_K, V, V^bad_mod, epsilon) satisfying clauses (a)--(f); Theorem A
  (iii) (line 822) states that relative to fixed initial Theta-data one has
  a collection of distinct Theta^{+-ell NF}-Hodge theaters indexed by Z,
  linked by the Theta-link chain (Corollaries 3.7 (i), 3.8).

  The repository carries two typed contracts for that single source object:

  * legacy contract `SourceInitialThetaData` (SourceInitialThetaData.lean
    :3004; candidate :345, clauses A--F at :1326, :1431, :1598, :1856,
    :2385, :2855).  Consumers: the D0--D11 ledger
    (Definition31D0D11FromSource.lean), the aligned ledger
    (Definition31D0D11Aligned.lean), the D3/D4 root
    (SourceDefinition31D3D4Root.lean), and the source family reduction
    (SourceHodgeTheaterFamilySourceReduction.lean).
  * current contract `SourceDefinition31Data`
    (SourceDefinition31Boundary.lean :660; component clauses at :39, :83,
    :203, :314, :445, :514, :605).  Consumers: Theorem311Source.OriginalInput
    (:41-46), H1FamilyPackage (SourceH1H2Construction.lean :273-278),
    SourceHodgeTheaterBridge.lean (:41), SourceRealizationLifting.lean
    (:46), SourceCompletionK1K2Wiring.lean (:57).

  Field comparison (paper object | legacy carrier | current carrier):

  1. arithmetic input (F, F-bar, K, E, l) | candidate.arithmetic (:345) |
     arithmetic (:661).  The same type `InitialThetaArithmeticData l` on
     both sides; this is the only definitionally shared component.
  2. X_F, C_F, X_K, C_K orbicurve objects | candidate.xF/cF/xK/cK (:347)
     over arithmetic.F / arithmetic.K | no counterpart; the current
     orbicurve clause (:445) carries a generic curve type only.
  3. selected and bad places | Vmod, VbadMod, VgoodMod as sets of places of
     F_mod with V bijective onto all places of F_mod (:351-357); Vmod is
     then provably everything (`Vmod_eq_univ`, :394) | selectedPlaces,
     badPlaces as arbitrary types with badIncluded, Nat labels,
     selectedNonempty, and Fintype badPlaces (:39-44, :662-663).
     Different carriers: the current side demands finiteness of bad places,
     the legacy side demands comap-compatibility of places.
  4. reduction and q-parameter | ClauseB.qParameter returns
     `FinitePlaceQCandidate p` (q in the adic completion, q != 0, valuation
     < 1; LocalQParameter.lean :39-47) with order coprime to l (:1450-1456)
     | reduction.qParameter : Bad -> Real with q != 0, ||q|| < 1, q != 1
     (:94-101).  An adic-valued Tate candidate against a real contraction
     law; no map between the two layers is supplied by either file.
  5. torsion and Galois image | ClauseC (:1598): rational 2- and 3-torsion,
     a module basis, a Galois representation *equal to the canonical one*
     (:1609-1612), SL2 containment inside the actual GL2 group (:1617) |
     SourceTorsionClause (:203): abstract torsionCarrier with a Fin 6
     label, a surjective representation into an abstract group, and opaque
     `imageContainsSL2`, `sixTorsionIndependent`, `lTorsionCompatible`.
  6. exact sequences and local groups | ClauseD (:1856): four profinite
     exact sequences with three embeddings; ClauseE (:2385): finite and
     infinite local data at every selected place | one exact sequence
     clause (:314) plus a section clause (:514) with a bijective section
     map and local group isomorphisms.
  7. cusp and epsilon | epsilonCarrier : Type with epsilon : epsilonCarrier
     (:365-366) and clauseF.cusp : SourceCuspDatum over that carrier
     (:2858; SourceCuspDatum :2637) | cusp.epsilon : Real with 0 < epsilon
     (:606-613) and cuspScale.
  8. maximal solvable extension | ClauseA.maximal_solvable_extension, an
     IntermediateField with its universal property (:1346-1355) | none.
  9. coherence slots | arithmetic_clause_coherence, clause_order_coherence
     (opaque propositions, :3012-3015) | five opaque
     arithmetic_*_compatibility slots (:670-679).

  Verdict.  The two contracts are not record-equivalent and neither is a
  projection of the other:
  * only item 1 has the same carrier on both sides;
  * items 2, 8 exist on the legacy side alone; items 4 and 6 carry typed
    local arithmetic on the legacy side that the current side replaces by
    abstract carriers;
  * items 3, 4, 6, 7 differ in carrier, and each side imposes at least one
    condition the other does not (bad-place finiteness only current;
    V-bijectivity and comap-compatibility only legacy; Real positivity of
    epsilon only current; maximal solvability only legacy);
  * items 5, 9 are typed on one side and opaque on the other.
  A mutual record bridge is therefore not constructible from the present
  fields.  What is proved in this file is the exact alignment layer that
  the downstream consumers read: the shared arithmetic root, its
  conservation and uniqueness laws, and the conditional assembly of a
  Hodge-theater family carrying both sides' arithmetic alignment at once.

  Cards, with the consumers they affect:
  * no record projection `SourceInitialThetaData -> SourceDefinition31Data`
    or back (card `IUT-I.definition31-contract-alignment`).  An old-to-
    current map would need new data that the legacy contract does not
    determine: the real q-parameter layer, the real cusp epsilon, and a
    torsion carrier with a Fin 6 label.  A current-to-old map would need
    the four orbicurve objects over arithmetic.F/K, the maximal solvable
    extension, the canonical Galois representation, and the per-place
    local data; none of these are fields of the current contract.
  * supply of an alignment instance.  `Definition31DualContractAlignment`
    requires a legacy and a current presentation of one source situation
    with equal arithmetic roots; whether the source supplies such a pair
    is source content, not proved here.

  Placement note.  This file sits in IUTI/HodgeTheater because its proved
  content is the family-side alignment transport; its imports point from
  the family layer down to the two InitialTheta contracts, keeping the
  existing folder dependency direction (HodgeTheater -> InitialTheta).
  No existing module imports this file.
-/

import LeanFormal.IUT.IUTI.HodgeTheater.SourceHodgeTheaterFamilySourceReduction
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

open LeanFormal.IUT.InitialThetaSource
open Theorem311Source

noncomputable section
/-! ## 1. The current-side projection of the Definition 3.1 root -/

/-- The arithmetic root of the current Definition 3.1 contract, presented
in the same shape as `sourceInitialThetaArithmetic` on the legacy side. -/
def sourceDefinition31Arithmetic {l : PrimeGeFive}
    (S : SourceDefinition31Data l) : InitialThetaArithmeticData l :=
  S.arithmetic

theorem sourceDefinition31Arithmetic_spec {l : PrimeGeFive}
    (S : SourceDefinition31Data l) :
    sourceDefinition31Arithmetic S = S.arithmetic :=
  rfl

/-! ## 2. The dual contract alignment -/

/-- A pair of presentations of one Definition 3.1 situation, one in each
in-repo contract, whose arithmetic roots agree.  This is the minimal datum
under which the two sides can be substituted for one another downstream. -/
structure Definition31DualContractAlignment (l : PrimeGeFive) where
  legacy : SourceInitialThetaData l
  current : SourceDefinition31Data l
  arithmetic_eq :
    sourceInitialThetaArithmetic legacy =
      sourceDefinition31Arithmetic current

namespace Definition31DualContractAlignment

variable {l : PrimeGeFive} (A : Definition31DualContractAlignment l)

/-- Field-level form of the shared-root agreement. -/
theorem arithmetic_agreement :
    A.legacy.candidate.arithmetic = A.current.arithmetic :=
  A.arithmetic_eq

/-- The shared-root agreement in the opposite orientation. -/
theorem arithmetic_agreement_symm :
    A.current.arithmetic = A.legacy.candidate.arithmetic :=
  A.arithmetic_eq.symm

/-- Conservation law: for alignments sharing their legacy side, the current
arithmetic root is determined; no second current presentation can drift. -/
theorem current_arithmetic_unique
    {B : Definition31DualContractAlignment l} (h : A.legacy = B.legacy) :
    A.current.arithmetic = B.current.arithmetic :=
  (A.arithmetic_eq.symm).trans
    ((congrArg sourceInitialThetaArithmetic h).trans B.arithmetic_eq)

/-- Conservation law, dual orientation: the legacy arithmetic root is
determined by any two alignments sharing their current side. -/
theorem legacy_arithmetic_unique
    {B : Definition31DualContractAlignment l} (h : A.current = B.current) :
    A.legacy.candidate.arithmetic = B.legacy.candidate.arithmetic :=
  (A.arithmetic_eq).trans
    ((congrArg sourceDefinition31Arithmetic h).trans B.arithmetic_eq.symm)

end Definition31DualContractAlignment
/-! ## 3. Existence of an alignment is exactly shared-root agreement -/

theorem definition31Alignment_exists_iff_shared_root {l : PrimeGeFive}
    (L : SourceInitialThetaData l) (C : SourceDefinition31Data l) :
    (∃ A : Definition31DualContractAlignment l,
        A.legacy = L ∧ A.current = C) ↔
      sourceInitialThetaArithmetic L = sourceDefinition31Arithmetic C := by
  constructor
  · rintro ⟨A, hL, hC⟩
    rw [← hL, ← hC]
    exact A.arithmetic_eq
  · intro h
    exact ⟨{ legacy := L, current := C, arithmetic_eq := h }, rfl, rfl⟩

/-- With disagreeing arithmetic roots, no alignment over the given pair
of presentations exists. -/
theorem no_definition31Alignment_of_arithmetic_ne {l : PrimeGeFive}
    (L : SourceInitialThetaData l) (C : SourceDefinition31Data l)
    (h : sourceInitialThetaArithmetic L ≠
      sourceDefinition31Arithmetic C) :
    ¬ ∃ A : Definition31DualContractAlignment l,
      A.legacy = L ∧ A.current = C :=
  fun hA => h ((definition31Alignment_exists_iff_shared_root L C).mp hA)

/-! ## 4. Transport of the consumer alignment predicates -/

/-- If a Hodge-theater family carries the current contract's arithmetic
root, it carries the legacy contract's root as well.  This is the exact
shape of `arithmetic_alignment` in `Theorem311Source.OriginalInput`
(:45-46) and in `H1FamilyPackage` (SourceH1H2Construction.lean :277). -/
theorem family_alignment_current_to_legacy {l : PrimeGeFive}
    (A : Definition31DualContractAlignment l) {V : Type*}
    (F : SourceHodgeTheaterFamily l V)
    (h : ∀ i, (F.theater i).arithmetic = A.current.arithmetic) :
    ∀ i, (F.theater i).arithmetic = A.legacy.candidate.arithmetic :=
  fun i => (h i).trans A.arithmetic_agreement_symm

/-- The converse transport. -/
theorem family_alignment_legacy_to_current {l : PrimeGeFive}
    (A : Definition31DualContractAlignment l) {V : Type*}
    (F : SourceHodgeTheaterFamily l V)
    (h : ∀ i, (F.theater i).arithmetic = A.legacy.candidate.arithmetic) :
    ∀ i, (F.theater i).arithmetic = A.current.arithmetic :=
  fun i => (h i).trans A.arithmetic_agreement

/-- Under a dual alignment the two alignment predicates are equivalent. -/
theorem family_alignment_iff {l : PrimeGeFive}
    (A : Definition31DualContractAlignment l) {V : Type*}
    (F : SourceHodgeTheaterFamily l V) :
    (∀ i, (F.theater i).arithmetic = A.current.arithmetic) ↔
      ∀ i, (F.theater i).arithmetic = A.legacy.candidate.arithmetic :=
  ⟨family_alignment_current_to_legacy A F,
    family_alignment_legacy_to_current A F⟩
/-! ## 5. Conditional assembly carrying both alignments at once -/

/-- The strip-supply assembly of
`SourceHodgeTheaterFamilySourceReduction.stripSpineFamily`, run on the
current contract's arithmetic root.  It is a `SourceHodgeTheaterFamily`
over any index type once an injective prime-strip family and its coherent
link system are supplied. -/
def alignedSpineFamily {l : PrimeGeFive}
    (A : Definition31DualContractAlignment l) (θ : FiniteThetaPacket l)
    {V : Type*} {I : Type*} (P : I → FPrimeStrip V)
    (hP : Function.Injective P) (E : FPrimeStripLinkSystem P) :
    SourceHodgeTheaterFamily l V :=
  stripSpineFamily A.current.arithmetic θ P hP E

theorem alignedSpineFamily_theater {l : PrimeGeFive}
    (A : Definition31DualContractAlignment l) (θ : FiniteThetaPacket l)
    {V : Type*} {I : Type*} (P : I → FPrimeStrip V)
    (hP : Function.Injective P) (E : FPrimeStripLinkSystem P) (i : I) :
    (alignedSpineFamily A θ P hP E).theater i =
      stripSpineTheater A.current.arithmetic θ P i :=
  rfl

/-- Every member of the assembled family carries the current arithmetic
root. -/
theorem alignedSpineFamily_current_alignment {l : PrimeGeFive}
    (A : Definition31DualContractAlignment l) (θ : FiniteThetaPacket l)
    {V : Type*} {I : Type*} (P : I → FPrimeStrip V)
    (hP : Function.Injective P) (E : FPrimeStripLinkSystem P) (i : I) :
    ((alignedSpineFamily A θ P hP E).theater i).arithmetic =
      A.current.arithmetic :=
  stripSpineFamily_arithmetic_alignment A.current.arithmetic θ P hP E i

/-- Every member of the assembled family carries the legacy arithmetic
root as well: one and the same family satisfies both contracts'
arithmetic alignment predicate. -/
theorem alignedSpineFamily_legacy_alignment {l : PrimeGeFive}
    (A : Definition31DualContractAlignment l) (θ : FiniteThetaPacket l)
    {V : Type*} {I : Type*} (P : I → FPrimeStrip V)
    (hP : Function.Injective P) (E : FPrimeStripLinkSystem P) (i : I) :
    ((alignedSpineFamily A θ P hP E).theater i).arithmetic =
      A.legacy.candidate.arithmetic :=
  (stripSpineFamily_arithmetic_alignment A.current.arithmetic θ P hP E
      i).trans A.arithmetic_agreement_symm

/-- The assembly satisfies both sides' consumer alignment shape at once. -/
theorem alignedSpineFamily_both_alignments {l : PrimeGeFive}
    (A : Definition31DualContractAlignment l) (θ : FiniteThetaPacket l)
    {V : Type*} {I : Type*} (P : I → FPrimeStrip V)
    (hP : Function.Injective P) (E : FPrimeStripLinkSystem P) :
    (∀ i, ((alignedSpineFamily A θ P hP E).theater i).arithmetic =
        A.current.arithmetic) ∧
      ∀ i, ((alignedSpineFamily A θ P hP E).theater i).arithmetic =
        A.legacy.candidate.arithmetic :=
  ⟨alignedSpineFamily_current_alignment A θ P hP E,
    alignedSpineFamily_legacy_alignment A θ P hP E⟩

/-- The legacy-side assembly route of
`SourceHodgeTheaterFamilySourceReduction` and the current-side route agree
as soon as the two arithmetic roots agree: the strip-supply family does
not depend on which contract supplies the root. -/
theorem sourceInitialThetaSpineFamily_eq_alignedSpineFamily
    {l : PrimeGeFive} (A : Definition31DualContractAlignment l)
    (θ : FiniteThetaPacket l) {I : Type*}
    (P : I → FPrimeStrip A.legacy.candidate.V)
    (hP : Function.Injective P) (E : FPrimeStripLinkSystem P) :
    sourceInitialThetaSpineFamily A.legacy θ P hP E =
      alignedSpineFamily A θ P hP E := by
  change stripSpineFamily (sourceInitialThetaArithmetic A.legacy) θ P hP E =
    stripSpineFamily (sourceDefinition31Arithmetic A.current) θ P hP E
  rw [A.arithmetic_eq]

end

end LeanFormal.IUT
namespace LeanFormal.IUT.Audit

def definition31ContractAlignment : Obligation :=
  { id := "IUT-I.definition31-contract-alignment"
    source :=
      "IUT I, Definition 3.1 (line 3122); Theorem A (iii) (line 822); " ++
        "IUT III Theorem 3.11 boundary"
    status := VerificationStatus.conditional
    note :=
      "Alignment of the two in-repo contracts for Definition 3.1. " ++
        "Proved: the current-side arithmetic root projection; the dual " ++
        "contract alignment carrier with its agreement and uniqueness " ++
        "(conservation) laws; the equivalence of existence of an " ++
        "alignment over a fixed pair with equality of the two arithmetic " ++
        "roots; transport of the family arithmetic alignment between the " ++
        "two contracts (the exact field shape of " ++
        "Theorem311Source.OriginalInput and H1FamilyPackage); and the " ++
        "conditional strip-supply assembly into a family whose members " ++
        "carry both sides' arithmetic roots simultaneously. Not asserted " ++
        "(card): record-level projections between SourceInitialThetaData " ++
        "and SourceDefinition31Data in either direction (the contracts " ++
        "differ in carriers and quantifiers as listed in the file " ++
        "header), and the supply of an alignment instance for a given " ++
        "source situation. Consumers: Theorem311Source.OriginalInput, " ++
        "SourceH1H2Construction.H1FamilyPackage, SourceHodgeTheaterBridge."
    dependsOn :=
      [ "IUT-I.initial-theta-source-definition31-boundary",
        "IUT-I.hodge-theater-family-source-reduction" ] }

end LeanFormal.IUT.Audit
