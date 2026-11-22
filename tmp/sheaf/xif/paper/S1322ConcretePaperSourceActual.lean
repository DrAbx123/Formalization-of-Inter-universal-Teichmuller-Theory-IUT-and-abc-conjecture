import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import tmp.sheaf.xif.paper.S1311PaperInd1PermutationLiftActual

/-!
# S1322: a concrete paper original input over the S1280 Gaussian D3/D4 source

S1280 constructs the actual Definition 3.1(a)(b)(e) data over the concrete
Gaussian arithmetic input `concreteGaussianInitialThetaArithmeticData l`:
the actual Q(i), the actual base-changed split multiplicative curve, the
actual finite place above 5, the actual bad-place selection, the actual
finite bad index, the actual reduction cards, and the actual place partition
and reduction clause.  Its first missing field is exactly

  torsion : SourceTorsionClause.{0,0,0} l.

This file attempts the next assembly step requested for the paper's original
input.  It does three things, and no more:

1.  It packages the exact remaining Definition 3.1 content as one gap: the D5
    torsion clause, the D6 orbicurve clause, the D7 sections clause, the D8
    cusp clause, and the five D9 (Prop, proof) compatibility pairs.  These
    are the literal clause types of `SourceDefinition31Data`; no field is
    replaced by `True`, `PUnit`, a constant, or an arbitrary basis.
2.  From exactly that gap it assembles, via the existing S1280 entry
    `S1280SourceData_of_remaining`, the concrete source data, and then the
    concrete `OriginalInput` of `sourceHaarActualOriginalInput`: identity
    family permutation on the index `Int x Int`, identity index equivalence,
    and the actual S1280 reduction clause.  The identity family admits the
    paper's Ind1 capsule lift at every row and capsule level, with the
    capsule permutation displayed as `Equiv.refl` (the proof is the concrete
    value behind `sourceHaarActual_lift`).
3.  It states the exact obstruction.  The paper-facing input exists if and
    only if the D5 clause and the D6-D8+D9 tail exist, and the first field is
    `SourceTorsionClause.{0,0,0} l`.  Thus no unconditional concrete input is
    claimed: D5 is the first missing source field, followed by D6, D7, D8,
    and the D9 pairs.

The first field is the outer Definition 3.1 field.  S1298 decomposes the
source-faithful D5 datum further: its first field is the rank-two basis
`(Fin 2 -> ZMod l.value) ~= E_F[l]`, and the large-image statement is open.
This file does not import S1298 and does not assert any D5 inhabitant.

At l = 5 the actual bad place above 5 has residue characteristic 5, and
S1280 proves that clause (c) `BadPlaceQParameterCards` is then refuted.  The
construction here is therefore a source-faithful paper input only for
l != 5; the arithmetic/reduction prefix itself is actual for every l.  The
refutation is restated below so the boundary is not hidden.

No D5-D8 clause is constructed and no D5-D8 inhabitant is asserted.  No
`sorry`, new axiom, `PUnit`, `True` gate, fake D5-D8 value, or arbitrary basis
is used.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1322ConcretePaperSourceActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1311PaperInd1PermutationLiftActual
open LeanFormal.IUT.XiFPaper.S1264SourceCapsuleInd1Actual
open LeanFormal.IUT.InitialThetaSource.TorsionCarrierReduction

variable {l : PrimeGeFive}

/-! ## 1. The exact remaining D5-D8 + D9 content -/

/-- D5, exactly the torsion field of `SourceDefinition31Data`. -/
abbrev S1322D5Field (l : PrimeGeFive) : Type 1 :=
  SourceTorsionClause.{0, 0, 0} l

/-- D6, exactly the orbicurve field of `SourceDefinition31Data`. -/
abbrev S1322D6Field : Type 1 :=
  SourceOrbicurveClause.{0, 0, 0}

/-- D7, exactly the sections field of `SourceDefinition31Data`. -/
abbrev S1322D7Field : Type 1 :=
  SourceSectionClause.{0, 0, 0}

/-- D8, exactly the cusp field of `SourceDefinition31Data`. -/
abbrev S1322D8Field : Type :=
  SourceCuspClause

/-- The D6-D8 clauses together with the five D9 `(Prop, proof)` pairs.  The
content of each D9 proposition is left exactly as the source contract leaves
it; no proposition is replaced by `True`. -/
structure S1322SourceGapTail (l : PrimeGeFive) where
  orbicurve : S1322D6Field
  sections : S1322D7Field
  cusp : S1322D8Field
  redCompat : Prop
  redCompat_proved : redCompat
  torCompat : Prop
  torCompat_proved : torCompat
  orbCompat : Prop
  orbCompat_proved : orbCompat
  secCompat : Prop
  secCompat_proved : secCompat
  cusCompat : Prop
  cusCompat_proved : cusCompat

/-- The exact source content still missing over the actual S1280 prefix.
Its first field is `torsion : SourceTorsionClause.{0,0,0} l`. -/
structure S1322SourceGap (l : PrimeGeFive) where
  torsion : S1322D5Field l
  tail : S1322SourceGapTail l

namespace S1322SourceGap

/-- The first field of the gap, definitionally the D5 torsion clause. -/
abbrev firstField (G : S1322SourceGap l) : S1322D5Field l := G.torsion

/-- Reassemble the S1280 remaining-clause package. -/
def toRemainingClauses (G : S1322SourceGap l) : S1280RemainingClauses l where
  torsion := G.torsion
  orbicurve := G.tail.orbicurve
  sections := G.tail.sections
  cusp := G.tail.cusp

/-- The actual Definition 3.1 data assembled from the S1280 actual D3/D4
prefix and exactly the gap.  The arithmetic, selected places, bad places,
and reduction components are the S1280 actual ones by definition. -/
def toSourceData (G : S1322SourceGap l) : SourceDefinition31Data.{0} l :=
  S1280SourceData_of_remaining l (G.toRemainingClauses)
    G.tail.redCompat G.tail.redCompat_proved
    G.tail.torCompat G.tail.torCompat_proved
    G.tail.orbCompat G.tail.orbCompat_proved
    G.tail.secCompat G.tail.secCompat_proved
    G.tail.cusCompat G.tail.cusCompat_proved

/-- The concrete `OriginalInput` over the assembled source data: the
identity-permutation Haar family of `SourceUnitRegionHaarDataActual`. -/
def toOriginalInput (G : S1322SourceGap l) :
    OriginalInput.{0, 0, 0, 0, 0} l Unit :=
  sourceHaarActualOriginalInput (l := l) G.toSourceData

/-- Exact decomposition: the gap is a D5 clause together with its D6-D8+D9
tail.  The first component is the first missing field. -/
def equivSigma :
    S1322SourceGap l ≃
      Sigma (fun _ : S1322D5Field l => S1322SourceGapTail l) where
  toFun G := ⟨G.torsion, G.tail⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv G := by cases G; rfl
  right_inv p := by cases p; rfl

end S1322SourceGap

/-! ## 2. Exact fields of the assembled `OriginalInput` -/

@[simp] theorem S1322SourceGap_toSourceData_arithmetic
    (G : S1322SourceGap l) :
    G.toSourceData.arithmetic = S1280Arithmetic l := rfl

@[simp] theorem S1322SourceGap_toSourceData_selectedPlaces
    (G : S1322SourceGap l) :
    G.toSourceData.selectedPlaces = Selected (S1280Selection l) := rfl

@[simp] theorem S1322SourceGap_toSourceData_badPlaces
    (G : S1322SourceGap l) :
    G.toSourceData.badPlaces = Bad (S1280Selection l) := rfl

@[simp] theorem S1322SourceGap_toSourceData_reduction
    (G : S1322SourceGap l) :
    G.toSourceData.reduction = S1280ReductionClause l := rfl

@[simp] theorem S1322SourceGap_toSourceData_torsion
    (G : S1322SourceGap l) :
    G.toSourceData.torsion = G.torsion := rfl

@[simp] theorem S1322SourceGap_toSourceData_orbicurve
    (G : S1322SourceGap l) :
    G.toSourceData.orbicurve = G.tail.orbicurve := rfl

@[simp] theorem S1322SourceGap_toSourceData_sections
    (G : S1322SourceGap l) :
    G.toSourceData.sections = G.tail.sections := rfl

@[simp] theorem S1322SourceGap_toSourceData_cusp
    (G : S1322SourceGap l) :
    G.toSourceData.cusp = G.tail.cusp := rfl

@[simp] theorem S1322SourceGap_toSourceData_redCompat
    (G : S1322SourceGap l) :
    G.toSourceData.arithmetic_reduction_compatibility =
      G.tail.redCompat := rfl

@[simp] theorem S1322SourceGap_toSourceData_torCompat
    (G : S1322SourceGap l) :
    G.toSourceData.arithmetic_torsion_compatibility =
      G.tail.torCompat := rfl

@[simp] theorem S1322SourceGap_toSourceData_orbCompat
    (G : S1322SourceGap l) :
    G.toSourceData.arithmetic_orbicurve_compatibility =
      G.tail.orbCompat := rfl

@[simp] theorem S1322SourceGap_toSourceData_secCompat
    (G : S1322SourceGap l) :
    G.toSourceData.arithmetic_section_compatibility =
      G.tail.secCompat := rfl

@[simp] theorem S1322SourceGap_toSourceData_cusCompat
    (G : S1322SourceGap l) :
    G.toSourceData.arithmetic_cusp_compatibility =
      G.tail.cusCompat := rfl

@[simp] theorem S1322SourceGap_toOriginalInput_initial
    (G : S1322SourceGap l) :
    G.toOriginalInput.initial = G.toSourceData := rfl

@[simp] theorem S1322SourceGap_toOriginalInput_family
    (G : S1322SourceGap l) :
    G.toOriginalInput.family =
      sourceHaarActualFamily (l := l) (S1280Arithmetic l) := rfl

@[simp] theorem S1322SourceGap_toOriginalInput_index_equiv
    (G : S1322SourceGap l) :
    G.toOriginalInput.index_equiv = Equiv.refl SourceTheorem311Index := rfl

@[simp] theorem S1322SourceGap_toOriginalInput_permutation
    (G : S1322SourceGap l) :
    G.toOriginalInput.family.permutation =
      Equiv.refl SourceTheorem311Index := rfl

theorem S1322SourceGap_toOriginalInput_initialTheta_arithmetic
    (G : S1322SourceGap l) :
    G.toOriginalInput.initial.toInitialThetaInput.arithmetic =
      S1280Arithmetic l := rfl

theorem S1322SourceGap_toOriginalInput_initialTheta_badPlaces
    (G : S1322SourceGap l) :
    G.toOriginalInput.initial.toInitialThetaInput.badPlaces =
      Bad (S1280Selection l) := rfl

/-! ## 3. The concrete identity capsule lift -/

/-- The chosen canonical capsule lift: at every row and capsule level the
capsule permutation is `Equiv.refl`.  This is a term of the lift structure,
not merely an existence statement. -/
def S1322SourceGap.canonicalLift (G : S1322SourceGap l)
    (n : Int) (j : Fin (capsuleLevels l)) :
    SourcePermutationCapsuleLift G.toOriginalInput n j where
  perm := Equiv.refl (Capsule j.val)
  index_compat := by
    intro i
    simp [S1322SourceGap.toOriginalInput, S1322SourceGap.toSourceData,
      S1322SourceGap.toRemainingClauses, sourceHaarActualOriginalInput,
      sourceHaarActualFamily, canonicalCapsuleTheaterAssignment,
      OriginalInput.indexOf]
    rfl

/-- The identity-permutation source input carries the canonical capsule lift
at every row and every capsule level, and the capsule permutation is
literally `Equiv.refl`.  This is the concrete value behind
`sourceHaarActual_lift`, not a new hypothesis. -/
theorem S1322SourceGap_toOriginalInput_lift_refl
    (G : S1322SourceGap l) (n : Int) (j : Fin (capsuleLevels l)) :
    ∃ L : SourcePermutationCapsuleLift G.toOriginalInput n j,
      L.perm = Equiv.refl (Capsule j.val) := by
  exact ⟨G.canonicalLift n j, rfl⟩

theorem S1322SourceGap.toOriginalInput_lift
    (G : S1322SourceGap l) (n : Int) (j : Fin (capsuleLevels l)) :
    Nonempty (SourcePermutationCapsuleLift G.toOriginalInput n j) :=
  sourceHaarActual_lift (l := l) G.toSourceData n j

/-! ## 4. The paper-facing original input -/

/-- A paper-facing original input: the actual `OriginalInput` over the
S1280 Gaussian D3/D4 prefix, the exact remaining gap that determines it,
the identification with the canonical assembly, and the Ind1 capsule lift at
every row and capsule level. -/
structure S1322PaperOriginalInput (l : PrimeGeFive) where
  gap : S1322SourceGap l
  input : OriginalInput.{0, 0, 0, 0, 0} l Unit
  input_eq : input = gap.toOriginalInput
  lift : ∀ (n : Int) (j : Fin (capsuleLevels l)),
    Nonempty (SourcePermutationCapsuleLift input n j)

namespace S1322PaperOriginalInput

def ofGap (G : S1322SourceGap l) : S1322PaperOriginalInput l where
  gap := G
  input := G.toOriginalInput
  input_eq := rfl
  lift := G.toOriginalInput_lift

def toGap (P : S1322PaperOriginalInput l) : S1322SourceGap l := P.gap

@[simp] theorem toGap_ofGap (G : S1322SourceGap l) :
    (ofGap G).toGap = G := rfl

@[simp] theorem ofGap_gap (G : S1322SourceGap l) :
    (ofGap G).gap = G := rfl

/-- The exact first missing field of a paper input. -/
abbrev firstField (P : S1322PaperOriginalInput l) : S1322D5Field l :=
  P.gap.torsion

/-- The gap's first field is literally the assembled input's torsion field:
the first missing field is not a new object but the actual Definition 3.1
torsion slot. -/
theorem firstField_eq_initial_torsion (P : S1322PaperOriginalInput l) :
    P.gap.torsion = P.input.initial.torsion := by
  rw [P.input_eq]
  rfl

theorem firstField_nonempty (P : S1322PaperOriginalInput l) :
    Nonempty (S1322D5Field l) :=
  ⟨P.firstField⟩

theorem input_arithmetic (P : S1322PaperOriginalInput l) :
    P.input.initial.arithmetic = S1280Arithmetic l := by
  rw [P.input_eq]
  rfl

theorem input_selectedPlaces (P : S1322PaperOriginalInput l) :
    P.input.initial.selectedPlaces = Selected (S1280Selection l) := by
  rw [P.input_eq]
  rfl

theorem input_badPlaces (P : S1322PaperOriginalInput l) :
    P.input.initial.badPlaces = Bad (S1280Selection l) := by
  rw [P.input_eq]
  rfl

theorem input_family (P : S1322PaperOriginalInput l) :
    P.input.family =
      sourceHaarActualFamily (l := l) (S1280Arithmetic l) := by
  rw [P.input_eq]
  rfl

theorem input_initialTheta_arithmetic (P : S1322PaperOriginalInput l) :
    P.input.initial.toInitialThetaInput.arithmetic = S1280Arithmetic l := by
  rw [P.input_eq]
  rfl

theorem input_initialTheta_badPlaces (P : S1322PaperOriginalInput l) :
    P.input.initial.toInitialThetaInput.badPlaces = Bad (S1280Selection l) := by
  rw [P.input_eq]
  rfl

/-- The concrete lift of a paper input is again the identity capsule
permutation. -/
theorem lift_refl (P : S1322PaperOriginalInput l) (n : Int)
    (j : Fin (capsuleLevels l)) :
    ∃ L : SourcePermutationCapsuleLift P.input n j,
      L.perm = Equiv.refl (Capsule j.val) := by
  rw [P.input_eq]
  exact S1322SourceGap_toOriginalInput_lift_refl P.gap n j

end S1322PaperOriginalInput

/-! ## 5. Exact obstruction: D5 is the first missing field -/

/-- The paper input exists if and only if the gap exists.  No hidden source
data is added by the identity family, the index equivalence, or the lift. -/
theorem S1322PaperOriginalInput_nonempty_iff_sourceGap :
    Nonempty (S1322PaperOriginalInput l) ↔
      Nonempty (S1322SourceGap l) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.gap⟩
  · rintro ⟨G⟩
    exact ⟨S1322PaperOriginalInput.ofGap G⟩

/-- Exact first-field decomposition of the gap. -/
theorem S1322SourceGap_nonempty_iff_firstField :
    Nonempty (S1322SourceGap l) ↔
      Nonempty (Sigma (fun _ : S1322D5Field l => S1322SourceGapTail l)) := by
  constructor
  · rintro ⟨G⟩
    exact ⟨⟨G.torsion, G.tail⟩⟩
  · rintro ⟨⟨T, tail⟩⟩
    exact ⟨⟨T, tail⟩⟩

/-- The paper-facing input exists exactly when the D5 torsion clause and the
D6-D8+D9 tail exist.  The D5 clause is the first component. -/
theorem S1322PaperOriginalInput_nonempty_iff_firstField :
    Nonempty (S1322PaperOriginalInput l) ↔
      Nonempty (S1322D5Field l) ∧ Nonempty (S1322SourceGapTail l) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨⟨P.gap.torsion⟩, ⟨P.gap.tail⟩⟩
  · rintro ⟨⟨T⟩, ⟨tail⟩⟩
    exact ⟨S1322PaperOriginalInput.ofGap ⟨T, tail⟩⟩

/-- The first missing field is exactly the S1280 first missing field, and
that field is exactly `SourceTorsionClause.{0,0,0} l`. -/
theorem S1322firstMissingField_eq :
    S1280FirstMissingField l = S1322D5Field l := rfl

/-- The D5 field is the outer first field; the source-faithful D5 datum of
S1298 begins with the rank-two torsion basis.  This is a type-level record of
the exact inner first field, not an existence assertion. -/
abbrev S1322D5InnerFirstField (l : PrimeGeFive) : Type :=
  (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
    (S1280Arithmetic l).curve.LTorsion l

def S1322D5Datum_firstField
    (D : SourceTorsionDatum l (S1280Arithmetic l)) :
    S1322D5InnerFirstField l :=
  D.torsion_basis

/-! ## 6. Clause (c) boundary at l = 5 -/

/-- S1280's clause-(c) boundary: at l = 5 the actual bad place above 5 is
not prime to l, and `BadPlaceQParameterCards` is refuted.  A source-faithful
instantiation of this paper input is therefore used with l != 5. -/
theorem S1322ClauseC_refuted_at_five :
    ¬ Nonempty (BadPlaceQParameterCards (S1280Selection S1280Five)) :=
  S1280_clauseC_refuted_at_five

/-! ## 7. Axiom footprint -/

#print axioms S1322SourceGap.toSourceData
#print axioms S1322SourceGap.toOriginalInput
#print axioms S1322SourceGap.canonicalLift
#print axioms S1322SourceGap_toOriginalInput_lift_refl
#print axioms S1322PaperOriginalInput.ofGap
#print axioms S1322PaperOriginalInput_nonempty_iff_firstField
#print axioms S1322firstMissingField_eq
#print axioms S1322ClauseC_refuted_at_five

end LeanFormal.IUT.XiFPaper.S1322ConcretePaperSourceActual

end
