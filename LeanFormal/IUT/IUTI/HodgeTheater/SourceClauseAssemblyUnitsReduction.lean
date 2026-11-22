/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31SignQuotientSupplyReduction
import Iut.Foundations.Orbicurve

/-!
  # Clause-assembly units of Definition 3.1 and the etale-stack unit

  Paper anchor (`papers\motizuki_corpus\text\Inter-universal Teichmuller
  Theory I.txt`):

  * Definition 3.1 opens the tuple `(F-bar/F, X_F, l, C_K, V, V^bad_mod,
    epsilon)` at extraction lines 3123-3125;
  * (b), lines 3131-3157: `X_F` is a once-punctured elliptic curve over
    `F` with stable reduction over all nonarchimedean places of `F`;
    `X_F -> C_F` is the stack-theoretic quotient of `X_F` by the unique
    `F`-involution `-1`; `V^bad_mod` is a nonempty set of nonarchimedean
    valuations of `F_mod` of odd residue characteristic such that `X_F`
    has bad (multiplicative) reduction at the places of `V(F)` lying over
    `V^bad_mod`;
  * (d), lines 3185-3215: `C_K` is a hyperbolic orbicurve of type
    `(1, l-tors)^±` over `K` with `K`-core `C_F x_F K`, together with
    `X_K` of type `(1, l-tors)` and the cartesian diagrams of finite etale
    coverings;
  * (e), lines 3216-3226: `V` is a subset of `V(K)` inducing a natural
    bijection `V ~-> V_mod`, i.e. a section of `V(K) --> V_mod`; each
    selected place carries the local cartesian diagrams;
  * (f), lines 3273-3283: `epsilon` is a cusp of `C_K` arising from a
    nonzero element of the quotient `Q` of [EtTh], Definition 2.1.

  Per-clause unit evaluation (this file):

  * Clause (e): the fields `selected_eq_V` and `selected_equiv` of
    `SourceClauseE` (`SourceDefinition31Quantifiers.lean:1391`) are the
    sign-quotient fields `S.V_eq_section` (`:612`) and `S.V_mod_bijection`
    (`:613`); the residual unit is the completion-level local family pair,
    and `SourceClauseE` is inhabited exactly when that pair is (section 1).
  * The local-curve component of each local source is pinned to the actual
    base change (`local_curve_eq_actual`), not free data (section 1).
  * Clause (b): the record is exactly the conjunction of its three
    arithmetic conditions; the coprimality conjunct follows from the
    moduli-level coprimality input of clause (c), lines 3179-3184
    (section 2).
  * Clause (d): no field is derivable from the arithmetic record; the
    witness tuple is the unit, and `SourceClauseD.ofKSideWitnesses`
    (`SourceClauseConstructors.lean:609`) consumes exactly it (comment
    only).
  * Clause (f): with the rank-one quotient fixed to the canonical K-side
    one, both binding fields become definitional; the residual unit is the
    boundary quadruple (section 3), whose assembly is sufficient for
    clause (f).  The converse is not claimed: an arbitrary clause (f)
    record need not carry the canonical origin map.
  * Assembly: the units assemble into `SourceClauseAssemblySupply`, hence
    -- with sign-quotient supply -- into the A2 gate (section 4).
  * Geometric core: `HyperbolicOrbicurve F` is inhabited exactly when one
    etale stack fiber with effective descent for the big etale topology
    exists; every geometric core supplies such fibers over `F` and `K`.
    No construction of `EtaleStackOverField` is present in the tree and
    Mathlib carries only the bare class `Pseudofunctor.IsStack`
    (`Mathlib/CategoryTheory/Sites/Descent/IsStack.lean:49`), so this is
    the named card `EtaleStackInstanceSupply` (section 5).

  Boundary: no RootLemmas import; the D11-E and D3/D4 lines are untouched.
  Placement: a HodgeTheater leaf; no module imports it.
-/

namespace LeanFormal.IUT

open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source

noncomputable section

universe u

variable {l : PrimeGeFive}

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-! ## 1. Clause (e): record-derived fields and the local-family unit -/

/-! `SourceClauseE` (`SourceDefinition31Quantifiers.lean:1391-1404`)
    asks for four fields.  The first two restate sign-quotient fields; the
    last two are the completion-level local diagrams, indexed by the
    actual selected place.  The unit below keeps only the latter. -/

structure SourceClauseELocalFamilyUnit
    {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l)
    (S : SourceSignQuotientData A)
    (C : SourceClauseA A S)
    (B : SourceClauseB A S C)
    (D : SourceClauseC A S C B)
    (K : SourceClauseD A S C B D) where
  finite_local :
    ∀ (v : {v : NumberFieldPlace A.K // v ∈ S.V})
      (hv : v.1.IsFinite),
      SourceFiniteLocalSource A S C B D K (selectedFinitePlace hv)
  infinite_local :
    ∀ (v : {v : NumberFieldPlace A.K // v ∈ S.V})
      (hv : v.1.IsInfinite),
      SourceInfiniteLocalSource A S C B D K (selectedInfinitePlace hv)

namespace SourceClauseELocalFamilyUnit

variable {A : InitialThetaArithmeticData.{u} l}
variable {S : SourceSignQuotientData A} {C : SourceClauseA A S}
variable {B : SourceClauseB A S C} {D : SourceClauseC A S C B}
variable {K : SourceClauseD A S C B D}

/-- Assemble clause (e) from the local-family unit; the two record-derived
fields are filled with the sign-quotient fields, as in
`SourceClauseE.ofLocalFamilies` (`SourceClauseConstructors.lean:799`). -/
noncomputable def assemble
    (U : SourceClauseELocalFamilyUnit A S C B D K) :
    SourceClauseE A S C B D K :=
  SourceClauseE.ofLocalFamilies (l := l) (A := A) (S := S) (C := C)
    (B := B) (D := D) (E := K) U.finite_local U.infinite_local

@[simp] theorem assemble_selected_eq_V
    (U : SourceClauseELocalFamilyUnit A S C B D K) :
    (assemble U).selected_eq_V = S.V_eq_section :=
  rfl

@[simp] theorem assemble_selected_equiv
    (U : SourceClauseELocalFamilyUnit A S C B D K) :
    (assemble U).selected_equiv = S.V_mod_bijection :=
  rfl

@[simp] theorem assemble_finite_local
    (U : SourceClauseELocalFamilyUnit A S C B D K) :
    (assemble U).finite_local = U.finite_local :=
  rfl

@[simp] theorem assemble_infinite_local
    (U : SourceClauseELocalFamilyUnit A S C B D K) :
    (assemble U).infinite_local = U.infinite_local :=
  rfl

/-- The `selected_eq_V` field of any clause (e) is the record field up to
proof irrelevance: it carries no free data. -/
theorem selected_eq_V_eq_record_field
    (L : SourceClauseE A S C B D K) :
    L.selected_eq_V = S.V_eq_section :=
  proof_irrel L.selected_eq_V S.V_eq_section

end SourceClauseELocalFamilyUnit

/-- Clause (e) is inhabited exactly when its residual local-family unit is:
the two record-derived fields add no choice. -/
theorem nonempty_sourceClauseE_iff_localFamilyUnit
    {A : InitialThetaArithmeticData.{u} l}
    {S : SourceSignQuotientData A} {C : SourceClauseA A S}
    {B : SourceClauseB A S C} {D : SourceClauseC A S C B}
    {K : SourceClauseD A S C B D} :
    Nonempty (SourceClauseE A S C B D K) ↔
      Nonempty (SourceClauseELocalFamilyUnit A S C B D K) :=
  ⟨fun ⟨L⟩ => ⟨⟨L.finite_local, L.infinite_local⟩⟩,
    fun ⟨U⟩ => ⟨U.assemble⟩⟩

namespace InitialThetaSource

/-- The local curve of a finite-place local source is pinned to the actual
base change; it is not free data. -/
theorem SourceFiniteLocalSource.localCurve_pinned
    {A : InitialThetaArithmeticData.{u} l}
    {S : SourceSignQuotientData A} {C : SourceClauseA A S}
    {B : SourceClauseB A S C} {D : SourceClauseC A S C B}
    {K : SourceClauseD A S C B D} {w : NumberField.FinitePlace A.K}
    (L : SourceFiniteLocalSource A S C B D K w) :
    L.localCurve = sourceFiniteLocalCurve A w :=
  L.local_curve_eq_actual

/-- The local curve of an infinite-place local source is pinned to the
actual base change; it is not free data. -/
theorem SourceInfiniteLocalSource.localCurve_pinned
    {A : InitialThetaArithmeticData.{u} l}
    {S : SourceSignQuotientData A} {C : SourceClauseA A S}
    {B : SourceClauseB A S C} {D : SourceClauseC A S C B}
    {K : SourceClauseD A S C B D} {w : NumberField.InfinitePlace A.K}
    (L : SourceInfiniteLocalSource A S C B D K w) :
    L.localCurve = sourceInfiniteLocalCurve A w :=
  L.local_curve_eq_actual

end InitialThetaSource

/-! ## 2. Clause (b): exact content and the cross-clause coprimality -/

/-- The exact content of `SourceClauseB` (`SourceDefinition31Quantifiers
.lean:918`): multiplicative reduction over the bad moduli places, a Tate
comparison over each such place, and coprimality of `l` with the residue
characteristics.  No field of the record is left out. -/
def SourceClauseBContent
    {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l)
    (S : SourceSignQuotientData A) : Prop :=
  (∀ p : NumberField.FinitePlace A.F,
      NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad →
      A.curve.HasMultiplicativeReductionAt p) ∧
  (∀ (p : NumberField.FinitePlace A.F)
      (hp : NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad),
      Nonempty (SourceTateComparisonWitness A p)) ∧
  (∀ (p : NumberField.FinitePlace A.F)
      (hp : NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad),
      Nat.Coprime l.value
        (NumberFieldFinitePlace.residueCharacteristic
          (NumberFieldFinitePlace.comap (k := A.Fmod) p)))

/-- Clause (b) over `A`, `S` is inhabited exactly when its content holds;
the record hides no further field, and the choice of clause (a) is
irrelevant to its content. -/
theorem nonempty_sourceClauseB_iff_content
    {A : InitialThetaArithmeticData.{u} l}
    {S : SourceSignQuotientData A} (C : SourceClauseA A S) :
    Nonempty (SourceClauseB A S C) ↔ SourceClauseBContent A S := by
  constructor
  · rintro ⟨B⟩
    exact ⟨B.multiplicative_over_bad, B.q_comparison,
      B.residue_characteristic_prime_to_l⟩
  · rintro ⟨hMultiplicative, hComparison, hCoprime⟩
    exact ⟨{ multiplicative_over_bad := hMultiplicative
             q_comparison := hComparison
             residue_characteristic_prime_to_l := hCoprime }⟩

/-- The coprimality conjunct of clause (b) follows from the moduli-level
coprimality input of clause (c), lines 3179-3184: for a place `p` of `F`
over a bad moduli place, the required coprime factor is the moduli place
itself. -/
theorem sourceClauseB_residue_coprime_of_moduli_coprime
    {A : InitialThetaArithmeticData.{u} l}
    {S : SourceSignQuotientData A}
    (h : ∀ q : NumberField.FinitePlace A.Fmod, q ∈ S.V_mod_bad →
      Nat.Coprime l.value
        (NumberFieldFinitePlace.residueCharacteristic q)) :
    ∀ (p : NumberField.FinitePlace A.F)
      (hp : NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad),
      Nat.Coprime l.value
        (NumberFieldFinitePlace.residueCharacteristic
          (NumberFieldFinitePlace.comap (k := A.Fmod) p)) :=
  fun p hp => h _ hp
/-! ## 3. Clause (f): the boundary unit and its assembly -/

/-- The residual unit of clause (f) after the canonical K-side quotient is
fixed: the cusp-origin map on the nonzero classes of the canonical rank-one
quotient, its value at the distinguished class, the cuspidal decomposition
of the K-side group data, and the agreement of its cusp with the origin.
This is exactly the explicit dependency of
`SourceClauseF.ofCanonicalBoundaryData` (`SourceClauseConstructors.lean
:981`). -/
structure SourceClauseFBoundaryUnit
    {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l)
    (S : SourceSignQuotientData A)
    (C : SourceClauseA A S)
    (B : SourceClauseB A S C)
    (D : SourceClauseC A S C B)
    (K : SourceClauseD A S C B D)
    (L : SourceClauseE A S C B D K) where
  originMap :
    {q : (SourceClauseF.canonicalKQuotientData (l := l) (A := A) (S := S)
      (C := C) (B := B) (D := D)).Quotient // q ≠ 0} →
      Iut.OrbicurveBoundaryCusp S.cK
  originMap_epsilon :
    originMap
        ⟨(SourceClauseF.canonicalKQuotientData (l := l) (A := A) (S := S)
          (C := C) (B := B) (D := D)).distinguishedClass,
          (SourceClauseF.canonicalKQuotientData (l := l) (A := A) (S := S)
            (C := C) (B := B) (D := D)).distinguishedClass_nonzero⟩ =
      S.epsilon
  cuspDecomposition :
    Iut.OrbicurveCuspidalDecompositionData K.c_groups.groups
  cuspDecomposition_cusp_eq_origin :
    cuspDecomposition.cusp =
      (SourceClauseF.ofCanonicalKBoundaryOrigin (l := l) (A := A) (S := S)
        (C := C) (B := B) (D := D) originMap originMap_epsilon).cusp

namespace SourceClauseFBoundaryUnit

variable {A : InitialThetaArithmeticData.{u} l}
variable {S : SourceSignQuotientData A} {C : SourceClauseA A S}
variable {B : SourceClauseB A S C} {D : SourceClauseC A S C B}
variable {K : SourceClauseD A S C B D} {L : SourceClauseE A S C B D K}

/-- Assemble clause (f) from the boundary unit.  The rank-one quotient is
the canonical K-side quotient, so `quotient_basis_eq_k_torsion_basis` and
`boundary_cusp_eq_epsilon` hold definitionally. -/
noncomputable def assemble
    (U : SourceClauseFBoundaryUnit A S C B D K L) :
    SourceClauseF A S C B D K L :=
  SourceClauseF.ofCanonicalBoundaryData (l := l) (A := A) (S := S) (C := C)
    (B := B) (D := D) (E := K) (L := L)
    U.originMap U.originMap_epsilon U.cuspDecomposition
    U.cuspDecomposition_cusp_eq_origin

@[simp] theorem assemble_basis_binding
    (U : SourceClauseFBoundaryUnit A S C B D K L) :
    (assemble U).boundary_origin.rank_one_quotient.torsion_basis =
      D.k_torsion_basis :=
  rfl

@[simp] theorem assemble_cusp_eq_epsilon
    (U : SourceClauseFBoundaryUnit A S C B D K L) :
    (assemble U).boundary_origin.cusp = S.epsilon :=
  rfl

/-- The boundary unit is sufficient for clause (f); the converse extraction
of a canonical origin map from an arbitrary clause (f) record is not
claimed. -/
theorem nonempty_sourceClauseF_of_boundaryUnit
    (U : SourceClauseFBoundaryUnit A S C B D K L) :
    Nonempty (SourceClauseF A S C B D K L) :=
  ⟨assemble U⟩

end SourceClauseFBoundaryUnit

/-! Clause (d) has no record-derived field: every entry is a K-side witness
object (sign action, quotient, quotient witness, morphism extension, finite
etale cover, group data, embeddings).  Its constructor
`SourceClauseD.ofKSideWitnesses` (`SourceClauseConstructors.lean:609`)
consumes exactly that tuple; no Lean unit is added here. -/

/-! ## 4. Assembly of the units into the clause assembly -/

/-- Assemble a full clause assembly from premises C, B, D, K (clauses (a)
through (d)), the local-family unit of clause (e), and the boundary unit of
clause (f) over the assembled clause (e). -/
noncomputable def clauseAssemblyOfUnits
    {A : InitialThetaArithmeticData.{u} l} {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {D : SourceClauseC A S C B} {K : SourceClauseD A S C B D}
    (U : SourceClauseELocalFamilyUnit A S C B D K)
    (FU : SourceClauseFBoundaryUnit A S C B D K U.assemble) :
    SourceClauseAssembly A S where
  clauseA := C
  clauseB := B
  clauseC := D
  clauseD := K
  clauseE := U.assemble
  clauseF := FU.assemble

/-- The unit chain (clauses (a)-(d) premises plus the two residual units)
is sufficient for `SourceClauseAssemblySupply`. -/
theorem sourceClauseAssemblySupply_of_unitChain
    (h : ∀ (A : InitialThetaArithmeticData.{u} l)
        (S : SourceSignQuotientData A),
        ∃ (C : SourceClauseA A S) (B : SourceClauseB A S C)
          (D : SourceClauseC A S C B) (K : SourceClauseD A S C B D)
          (U : SourceClauseELocalFamilyUnit A S C B D K),
          Nonempty (SourceClauseFBoundaryUnit A S C B D K U.assemble)) :
    SourceClauseAssemblySupply.{u} l := by
  intro A S
  obtain ⟨C, B, D, K, U, hFU⟩ := h A S
  obtain ⟨FU⟩ := hFU
  exact ⟨clauseAssemblyOfUnits U FU⟩

/-- The A2 gate from sign-quotient supply and the unit chain; the clause
assembly enters only through its sufficiency direction. -/
theorem sourceNativeArithmeticToSourceGate_of_signQuotientSupply_of_unitChain
    (hS : SourceSignQuotientSupply.{u} l)
    (hU : ∀ (A : InitialThetaArithmeticData.{u} l)
        (S : SourceSignQuotientData A),
        ∃ (C : SourceClauseA A S) (B : SourceClauseB A S C)
          (D : SourceClauseC A S C B) (K : SourceClauseD A S C B D)
          (U : SourceClauseELocalFamilyUnit A S C B D K),
          Nonempty (SourceClauseFBoundaryUnit A S C B D K U.assemble)) :
    SourceNativeArithmeticToSourceGate.{u} l :=
  (sourceNativeArithmeticToSourceGate_iff_witnessSupply (l := l)).mpr
    (sourceNativeWitnessSupply_of_signQuotientSupply_of_clauseAssemblySupply
      hS (sourceClauseAssemblySupply_of_unitChain hU))

/-! ## 5. The geometric core: one etale-stack fiber is the residual unit -/

/-- One etale stack fiber over `F` with effective descent for the big etale
topology on `SchemeOverField F` (`Iut/Foundations/Orbicurve.lean:116-120`).
This is the single unit that neither the repository nor Mathlib supplies:
no construction of `EtaleStackOverField` is present in the tree, and
Mathlib carries the bare class `Pseudofunctor.IsStack`
(`Mathlib/CategoryTheory/Sites/Descent/IsStack.lean:49`) with no instance
and no bridging lemma from sheaves to discrete-category stacks. -/
def EtaleStackInstanceSupply (F : Type u) [Field F] : Prop :=
  ∃ fiber : Iut.EtaleStackPseudofunctor F,
    fiber.IsStack (Iut.SchemeOverField.etaleTopology F)

/-- Conditional assembly: a stack fiber with a realized hyperbolic
signature yields a `HyperbolicOrbicurve`; the signature certificate is
inserted by construction and adds no choice. -/
noncomputable def realizedHyperbolicOrbicurve
    (F : Type u) [Field F]
    (fiber : Iut.EtaleStackPseudofunctor F)
    (isStack : fiber.IsStack (Iut.SchemeOverField.etaleTopology F))
    (signature : Iut.OrbicurveSignature)
    (hyperbolic : signature.IsHyperbolic) :
    Iut.HyperbolicOrbicurve F where
  stack :=
    { fiber := fiber
      isStack := isStack
      orbicurveSignature := some signature }
  geometry :=
    { signature := signature
      realizes_signature := rfl
      hyperbolic := hyperbolic }

@[simp] theorem realizedHyperbolicOrbicurve_signature
    (F : Type u) [Field F]
    (fiber : Iut.EtaleStackPseudofunctor F)
    (isStack : fiber.IsStack (Iut.SchemeOverField.etaleTopology F))
    (signature : Iut.OrbicurveSignature)
    (hyperbolic : signature.IsHyperbolic) :
    (realizedHyperbolicOrbicurve F fiber isStack signature hyperbolic).signature =
      signature :=
  rfl

@[simp] theorem realizedHyperbolicOrbicurve_stack_fiber
    (F : Type u) [Field F]
    (fiber : Iut.EtaleStackPseudofunctor F)
    (isStack : fiber.IsStack (Iut.SchemeOverField.etaleTopology F))
    (signature : Iut.OrbicurveSignature)
    (hyperbolic : signature.IsHyperbolic) :
    (realizedHyperbolicOrbicurve F fiber isStack signature hyperbolic).stack.fiber =
      fiber :=
  rfl

/-- `HyperbolicOrbicurve F` is inhabited exactly when one etale stack
fiber exists: the wrapper, the signature certificate and the wrapping are
free, and the once-punctured-elliptic signature is hyperbolic
(`Iut/Foundations/Orbicurve.lean:102`). -/
theorem nonempty_hyperbolicOrbicurve_iff_stackInstanceSupply
    (F : Type u) [Field F] :
    Nonempty (Iut.HyperbolicOrbicurve F) ↔ EtaleStackInstanceSupply F := by
  constructor
  · rintro ⟨X⟩
    exact ⟨X.stack.fiber, X.stack.isStack⟩
  · rintro ⟨fiber, hStack⟩
    exact ⟨realizedHyperbolicOrbicurve F fiber hStack
      Iut.OrbicurveSignature.oncePuncturedElliptic
      Iut.OrbicurveSignature.oncePuncturedElliptic_isHyperbolic⟩

/-- Any prescribed hyperbolic signature is realized over a supplied stack
fiber. -/
theorem exists_hyperbolicOrbicurve_signature_of_stackInstanceSupply
    (F : Type u) [Field F] (inst : EtaleStackInstanceSupply F)
    (signature : Iut.OrbicurveSignature)
    (hyperbolic : signature.IsHyperbolic) :
    ∃ X : Iut.HyperbolicOrbicurve F, X.signature = signature := by
  obtain ⟨fiber, hStack⟩ := inst
  exact ⟨realizedHyperbolicOrbicurve F fiber hStack signature hyperbolic, rfl⟩

/-- The `F`-side once-punctured-elliptic signature of Definition 3.1(b) is
available over a supplied stack fiber. -/
theorem exists_hyperbolicOrbicurve_oncePuncturedElliptic_of_stackInstanceSupply
    (F : Type u) [Field F] (inst : EtaleStackInstanceSupply F) :
    ∃ X : Iut.HyperbolicOrbicurve F,
      X.signature = Iut.OrbicurveSignature.oncePuncturedElliptic :=
  exists_hyperbolicOrbicurve_signature_of_stackInstanceSupply F inst _
    Iut.OrbicurveSignature.oncePuncturedElliptic_isHyperbolic

/-- The `K`-side `(1, l-tors)` signature of Definition 3.1(d) is available
over a supplied stack fiber. -/
theorem exists_hyperbolicOrbicurve_sourceTypeOneLTorsion_of_stackInstanceSupply
    {l : PrimeGeFive} (F : Type u) [Field F]
    (inst : EtaleStackInstanceSupply F) :
    ∃ X : Iut.HyperbolicOrbicurve F,
      X.signature = sourceTypeOneLTorsion l :=
  exists_hyperbolicOrbicurve_signature_of_stackInstanceSupply F inst _
    (sourceTypeOneLTorsion_hyperbolic l)

/-- Every geometric core supplies etale stack fibers over `F` and over
`K`; the stack unit is therefore a necessary condition of the
geometric-core card. -/
theorem etaleStackInstanceSupply_of_geometricCore
    {A : InitialThetaArithmeticData.{u} l}
    (G : SourceSignQuotientGeometricCore A) :
    EtaleStackInstanceSupply A.F ∧ EtaleStackInstanceSupply A.K :=
  ⟨⟨G.xF.stack.fiber, G.xF.stack.isStack⟩,
    ⟨G.xK.stack.fiber, G.xK.stack.isStack⟩⟩

/-- The stack unit over both source fields, uniformly in the arithmetic
root: the part of the geometric-core card that has no construction. -/
def GeometricCoreStackUnit (l : PrimeGeFive) : Prop :=
  ∀ A : InitialThetaArithmeticData.{u} l,
    EtaleStackInstanceSupply A.F ∧ EtaleStackInstanceSupply A.K

/-- The geometric-core supply implies the stack unit over both fields. -/
theorem geometricCoreStackUnit_of_geometricCoreSupply
    (h : SourceSignQuotientGeometricCoreSupply.{u} l) :
    GeometricCoreStackUnit.{u} l := by
  intro A
  obtain ⟨G⟩ := h A
  exact etaleStackInstanceSupply_of_geometricCore G

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def definition31ClauseAssemblyUnitsReduction : Obligation :=
  { id := "IUT-I.definition-3.1-clause-assembly-units-reduction"
    source :=
      "IUT I, Definition 3.1(b),(d),(e),(f); extraction lines 3131-3283"
    status := VerificationStatus.interface
    note :=
      "Clause-assembly unit evaluation. Proved: (1) clause (e) is " ++
        "inhabited exactly when its completion-level local family unit " ++
        "is, its two remaining fields being the sign-quotient fields; " ++
        "(2) each local curve is pinned to the actual base change; " ++
        "(3) clause (b) is exactly the conjunction of its three " ++
        "arithmetic conditions, whose coprimality conjunct follows from " ++
        "the moduli-level coprimality input of clause (c); (4) clause (f) " ++
        "assembles from the named boundary unit over the canonical K-side " ++
        "quotient, its two binding fields being definitional; (5) the " ++
        "units assemble into clause-assembly supply and, with " ++
        "sign-quotient supply, into the A2 gate. Cards: the clause (d) " ++
        "K-side witness tuple; the boundary unit (sufficiency only); the " ++
        "etale-stack card -- HyperbolicOrbicurve F is inhabited exactly " ++
        "when one etale stack fiber with effective descent exists, and no " ++
        "such construction is present in the repository or in Mathlib. " ++
        "Boundary: no RootLemmas import; D11-E and D3/D4 untouched. " ++
        "Consumers: SourceHodgeTheaterBridge, D3.1 SourceOriginalInput, " ++
        "SourceH1H2Construction."
    dependsOn :=
      [ "IUT-I.definition-3.1-sign-quotient-supply-reduction",
        "IUT-I.definition-3.1-A2-clause-constructors",
        "IUT-I.definition-3.1-A2-quantifier-boundary" ] }

end LeanFormal.IUT.Audit
