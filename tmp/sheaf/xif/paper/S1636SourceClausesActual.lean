import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual
import tmp.sheaf.xif.paper.S1428RealCuspValuationActual

/-!
# S1636: actual Definition 3.1 clause components over the Gaussian data

This file assembles the three Definition 3.1 clauses that were still open after
S1280/S1319/S1320/S1348/S1419/S1428:

* `SourceOrbicurveClause` (D6);
* `SourceSectionClause` (D7);
* `SourceCuspClause` (D8).

The construction is literal: every field that the actual Gaussian data
determines is one of the already constructed actual objects, and the remaining
input is stated as an exact first missing structure.  No toy carrier, terminal
stack, `True`, `PUnit`, `sorry` or new axiom is used.

## D6 orbicurve

The point-level clause fields are the actual S1348 fields over the S1280
Gaussian arithmetic input: the actual projective curve points, the actual
punctured points, the actual degree-two finite-etale cover
`S1348Cover = Spec (R (x)_K (K x K))`, its actual structure group and
surjective cover map, the actual once-punctured cusp count, and the actual
cover-surjectivity compatibility.

The stack-level actual object is `S1419Orbicurve l`, the nonterminal
hyperbolic orbicurve over `S1348K l = (S1280Arithmetic l).F` with signature
`oncePuncturedElliptic` (S1419).  The exact-sequence slot of the record is the
one place where the stack object enters.  Its literal first missing structure is

```
  Iut.OrbicurveFundamentalGroupData (S1419Orbicurve l)
    (Iut.AbsoluteGaloisProfinite (S1348K l)).
```

From that structure the full clause is constructed by
`S1348ClauseOfFirstField`; its exact-sequence cover group is the arithmetic
orbicurve fundamental group supplied by the structure, and its base group is
the actual absolute Galois group of `S1348K l`.  The l-torsion sequence
`S1319LTorsionExactSequence` is deliberately not used as a substitute: its base
group is the range of the l-torsion representation, not the absolute Galois
group, and it is not the orbifold Pi sequence.

## D7 section

The place-section half is actual: `S1320Layer l` is the canonical
restriction/lift section of the identity tower `Fmod = F = K = Q(i)`, with
bijective section map.  The one missing half is exactly the local-group carrier
family `localGroupCarrier : valuationCarrier -> Type` (D7b); the dependent tail
is `S1320D7Tail`.  `S1320D7SupplyEquiv` is the exact first-field/tail
decomposition.

## D8 cusp

The actual geometric cusp is the puncture `[0 : 1 : 0]` of the concrete
split multiplicative curve, and the actual q-parameter norm is `1/5`.  The
current clause field is a real `epsilon`; neither the cusp point nor
`log q` is a real cusp coordinate.  The faithful actual route is the S1428
valuation construction: for a paper sign-quotient datum `S` (the D9 object;
constructing `S` itself is outside this file) and a nonzero cusp local
parameter in the actual completion at the place above 5, the construction gives
`epsilon = ‖localParameter c‖` and `cuspScale = epsilon⁻¹`.  The exact
missing structure is therefore the S1428 cusp local parameter (equivalently the
S1330 real cusp coordinate on the paper cusp); `epsilonReal` is not chosen
arbitrarily.

## Consumer

`S1636RemainingClauses` is literally the `S1280RemainingClauses` package
consumed by `S1280SourceData_of_remaining`; its orbicurve, sections and cusp
projections are definitionally the clauses constructed here.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1636SourceClausesActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.InitialThetaSource.Definition31D4D9Supply
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1319OrbicurveClauseActual
open LeanFormal.IUT.XiFPaper.S1320SectionsCuspActual
open LeanFormal.IUT.XiFPaper.S1330CuspEpsilonActual
open LeanFormal.IUT.XiFPaper.S1331OrbicurveClauseAudit
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1428RealCuspValuationActual

variable (l : PrimeGeFive)

/-! ## 1. D6: the actual S1419 orbicurve and the exact first missing groups -/

/-- The actual Gaussian field of the S1280/S1348 input. -/
abbrev S1636K : Type := S1348K l

/-- The concrete Gaussian root has `F = K = Q(i)`: this is why the S1419
orbicurve over `F` is literally the first component of the D6 first field,
which S1348 states over `K`. -/
theorem S1636K_eq_F : S1636K l = (S1280Arithmetic l).F := rfl

theorem S1636K_eq_K : S1636K l = (S1280Arithmetic l).K := rfl

/-- The actual S1419 nonterminal hyperbolic orbicurve over the Gaussian field. -/
noncomputable abbrev S1636Orbicurve : Iut.HyperbolicOrbicurve (S1636K l) :=
  S1419Orbicurve l

/-- The S1419 orbicurve has the paper's once-punctured elliptic signature. -/
theorem S1636Orbicurve_signature :
    (S1636Orbicurve l).signature =
      Iut.OrbicurveSignature.oncePuncturedElliptic :=
  S1419Orbicurve_signature l

/-- The S1419 orbicurve is nonterminal: it is not a point fiber. -/
theorem S1636Orbicurve_nonterminal :
    S1319NonterminalFiber (S1636Orbicurve l) :=
  S1419NonterminalFiber l

/-- Exact first missing structure of the D6 clause: certified orbifold
fundamental-group data over the actual S1419 orbicurve and the actual absolute
Galois group of `S1348K l`. -/
abbrev S1636OrbicurveFirstMissing : Type 1 :=
  Iut.OrbicurveFundamentalGroupData (S1636Orbicurve l)
    (Iut.AbsoluteGaloisProfinite (S1348K l))

/-- The literal D6 first field of S1348: an actual hyperbolic orbicurve with its
certified group data. -/
abbrev S1636OrbicurveExactField : Type 1 :=
  S1348D6FirstMissingField l

/-- The S1419 orbicurve together with the supplied group data, as the literal
S1348 first field. -/
noncomputable def S1636OrbicurveExactFieldOfGroups
    (groups : S1636OrbicurveFirstMissing l) : S1636OrbicurveExactField l :=
  S1419D6FirstMissingFieldOfGroups l groups

@[simp] theorem S1636OrbicurveExactFieldOfGroups_fst
    (groups : S1636OrbicurveFirstMissing l) :
    (S1636OrbicurveExactFieldOfGroups l groups).1 = S1636Orbicurve l := rfl

/-- **The actual D6 clause.**  All point-level fields are the actual S1348
objects; the exact-sequence slot is the exact missing S1419 orbifold
fundamental-group data. -/
noncomputable def S1636OrbicurveClause
    (groups : S1636OrbicurveFirstMissing l) : SourceOrbicurveClause.{0, 0, 0} :=
  S1348ClauseOfFirstField l (S1636OrbicurveExactFieldOfGroups l groups)

@[simp] theorem S1636OrbicurveClause_curve
    (groups : S1636OrbicurveFirstMissing l) :
    (S1636OrbicurveClause l groups).curve = S1331ClauseCurve l := rfl

@[simp] theorem S1636OrbicurveClause_puncturedCurve
    (groups : S1636OrbicurveFirstMissing l) :
    (S1636OrbicurveClause l groups).puncturedCurve =
      S1331ClausePuncturedCurve l := rfl

@[simp] theorem S1636OrbicurveClause_curveToPunctured
    (groups : S1636OrbicurveFirstMissing l) :
    (S1636OrbicurveClause l groups).curveToPunctured =
      S1331ClauseCurveToPunctured l := rfl

@[simp] theorem S1636OrbicurveClause_cover
    (groups : S1636OrbicurveFirstMissing l) :
    (S1636OrbicurveClause l groups).cover = S1348Cover l := rfl

@[simp] theorem S1636OrbicurveClause_coverToPunctured
    (groups : S1636OrbicurveFirstMissing l) :
    (S1636OrbicurveClause l groups).coverToPunctured =
      S1348CoverToPunctured l := rfl

@[simp] theorem S1636OrbicurveClause_structureGroup
    (groups : S1636OrbicurveFirstMissing l) :
    (S1636OrbicurveClause l groups).structureGroup = S1348StructureGroup l := rfl

@[simp] theorem S1636OrbicurveClause_cuspCount
    (groups : S1636OrbicurveFirstMissing l) :
    (S1636OrbicurveClause l groups).cuspCount = 1 := rfl

@[simp] theorem S1636OrbicurveClause_exactSequence_coverGroup
    (groups : S1636OrbicurveFirstMissing l) :
    (S1636OrbicurveClause l groups).exactSequence.coverGroup =
      ↥groups.arithmeticGroup := rfl

@[simp] theorem S1636OrbicurveClause_exactSequence_geometricGroup
    (groups : S1636OrbicurveFirstMissing l) :
    (S1636OrbicurveClause l groups).exactSequence.geometricGroup =
      ↥groups.geometric.group := rfl

@[simp] theorem S1636OrbicurveClause_exactSequence_baseGroup
    (groups : S1636OrbicurveFirstMissing l) :
    (S1636OrbicurveClause l groups).exactSequence.baseGroup =
      S1331ExactSequenceBaseGroup l := rfl

/-- The D6 clause uses the actual degree-two finite-etale cover: the cover is
not a subsingleton / not PUnit. -/
theorem S1636OrbicurveClause_cover_not_subsingleton
    (groups : S1636OrbicurveFirstMissing l) :
    ¬ Subsingleton (S1636OrbicurveClause l groups).cover :=
  S1348Cover_not_subsingleton l

/-- The D6 clause does not use the identity cover. -/
theorem S1636OrbicurveClause_cover_not_injective
    (groups : S1636OrbicurveFirstMissing l) :
    ¬ Function.Injective (S1636OrbicurveClause l groups).coverToPunctured :=
  S1348CoverToPunctured_not_injective l

/-- The D6 curve is the actual nontrivial curve carrier, not a point. -/
theorem S1636OrbicurveClause_curve_not_subsingleton
    (groups : S1636OrbicurveFirstMissing l) :
    ¬ Subsingleton (S1636OrbicurveClause l groups).curve :=
  S1331ClauseCurve_not_subsingleton l

/-- The D6 exact-sequence base group is the actual absolute Galois group. -/
theorem S1636OrbicurveClause_baseGroup_nonempty
    (groups : S1636OrbicurveFirstMissing l) :
    Nonempty (S1636OrbicurveClause l groups).exactSequence.baseGroup :=
  S1331ExactSequenceBaseGroup_nonempty l

/-! ## 2. D7: actual place-section layer and exact D7b local-group field -/

/-- The actual canonical place-section layer of the Gaussian arithmetic input. -/
noncomputable abbrev S1636SectionLayer :
    SourceValuationSectionLayer (S1280Arithmetic l) :=
  S1320Layer l

/-- Exact first missing field of D7b: the local-group carrier family over the
actual place-section carrier.  It is the first ray of the curve-side
`Pi_Xv/Pi_Cv` data, not an arithmetic local Galois group. -/
abbrev S1636SectionFirstMissing : Type 1 :=
  S1320D7FirstField l

/-- The exact D7b intake: the first field together with its dependent tail. -/
abbrev S1636SectionSupply : Type 1 :=
  D7LocalGroupSectionSupply.{0, 0} (S1320Layer l)

/-- Exact decomposition of the D7b intake into its first field and tail. -/
noncomputable def S1636SectionSupplyEquiv :
    S1636SectionSupply l ≃
      Σ G0 : S1636SectionFirstMissing l, S1320D7Tail l G0 :=
  S1320D7SupplyEquiv l

/-- Nonemptiness of D7b is exactly first field plus tail. -/
theorem S1636SectionSupply_nonempty_iff :
    Nonempty (S1636SectionSupply l) ↔
      ∃ G0 : S1636SectionFirstMissing l,
        Nonempty (S1320D7Tail l G0) :=
  S1320D7Supply_nonempty_iff_firstField_tail l

/-- **The actual D7 clause.**  The six place-section fields are the canonical
actual layer; the local-group half is exactly the supplied D7b intake. -/
noncomputable def S1636SectionClause
    (G : S1636SectionSupply l) : SourceSectionClause.{0, 0, 0} :=
  S1320SectionClauseOfSupply l G

@[simp] theorem S1636SectionClause_valuationCarrier
    (G : S1636SectionSupply l) :
    (S1636SectionClause l G).valuationCarrier =
      (S1636SectionLayer l).valuationCarrier := rfl

@[simp] theorem S1636SectionClause_modifiedValuationCarrier
    (G : S1636SectionSupply l) :
    (S1636SectionClause l G).modifiedValuationCarrier =
      (S1636SectionLayer l).modifiedValuationCarrier := rfl

@[simp] theorem S1636SectionClause_sectionMap
    (G : S1636SectionSupply l) :
    (S1636SectionClause l G).sectionMap =
      (S1636SectionLayer l).sectionMap := rfl

@[simp] theorem S1636SectionClause_sectionRightInverse
    (G : S1636SectionSupply l) :
    (S1636SectionClause l G).sectionRightInverse =
      (S1636SectionLayer l).sectionRightInverse := rfl

@[simp] theorem S1636SectionClause_localGroupCarrier
    (G : S1636SectionSupply l) :
    (S1636SectionClause l G).localGroupCarrier = G.localGroupCarrier := rfl

@[simp] theorem S1636SectionClause_localGroupSection
    (G : S1636SectionSupply l) :
    (S1636SectionClause l G).localGroupSection = G.localGroupSection := rfl

/-- The actual place-section map is bijective. -/
theorem S1636SectionClause_sectionMap_bijective
    (G : S1636SectionSupply l) :
    Function.Bijective (S1636SectionClause l G).sectionMap :=
  S1320SectionMap_bijective l

/-- The six-field prefix of the constructed clause is literally the actual
place-section prefix. -/
theorem S1636SectionClause_prefix
    (G : S1636SectionSupply l) :
    S1320ClausePrefix (S1636SectionClause l G) = S1320ActualPrefix l := rfl

/-! ## 3. D8: actual cusp data and the exact real-coordinate input -/

/-- The paper cusp carrier over a sign-quotient datum `S`. -/
abbrev S1636PaperCusp
    (S : SourceSignQuotientData (S1280Arithmetic l)) : Type 1 :=
  S1330PaperCusp l S

/-- Exact first missing structure of the faithful real cusp coordinate: a real
coordinate package on the paper cusp. -/
abbrev S1636CuspCoordinateFirstMissing
    (S : SourceSignQuotientData (S1280Arithmetic l)) : Type 1 :=
  S1330RealCuspCoordinate l S

/-- A faithful real cusp coordinate produces the D8 clause at the selected
paper cusp. -/
noncomputable def S1636CuspClauseOfRealCuspCoordinate
    (S : SourceSignQuotientData (S1280Arithmetic l))
    (R : S1636CuspCoordinateFirstMissing l S)
    (c : S1636PaperCusp l S) : SourceCuspClause :=
  S1330CuspClauseOfRealCuspCoordinate R c

/-- Exact first missing actual source of the real cusp coordinate: a nonzero
cusp local parameter in the actual completion at the place above 5. -/
abbrev S1636CuspLocalParameterFirstMissing
    (S : SourceSignQuotientData (S1280Arithmetic l)) : Type 1 :=
  S1428CuspLocalParameter l S

/-- **The actual D8 clause from the S1428 local parameter.**  The value of
`epsilon` is the norm of the local parameter at the selected cusp; the cusp
scale is its inverse.  No arbitrary real is chosen. -/
noncomputable def S1636CuspClauseOfLocalParameter
    (S : SourceSignQuotientData (S1280Arithmetic l))
    (P : S1636CuspLocalParameterFirstMissing l S)
    (c : S1636PaperCusp l S) : SourceCuspClause :=
  S1636CuspClauseOfRealCuspCoordinate l S
    (S1428ValuationRealCuspCoordinate P) c

@[simp] theorem S1636CuspClauseOfLocalParameter_epsilon
    (S : SourceSignQuotientData (S1280Arithmetic l))
    (P : S1636CuspLocalParameterFirstMissing l S)
    (c : S1636PaperCusp l S) :
    (S1636CuspClauseOfLocalParameter l S P c).epsilon =
      ‖P.localParameter c‖ := rfl

@[simp] theorem S1636CuspClauseOfLocalParameter_cuspScale
    (S : SourceSignQuotientData (S1280Arithmetic l))
    (P : S1636CuspLocalParameterFirstMissing l S)
    (c : S1636PaperCusp l S) :
    (S1636CuspClauseOfLocalParameter l S P c).cuspScale =
      (‖P.localParameter c‖)⁻¹ := rfl

theorem S1636CuspClauseOfLocalParameter_epsilon_ne_zero
    (S : SourceSignQuotientData (S1280Arithmetic l))
    (P : S1636CuspLocalParameterFirstMissing l S)
    (c : S1636PaperCusp l S) :
    (S1636CuspClauseOfLocalParameter l S P c).epsilon ≠ 0 := by
  rw [S1636CuspClauseOfLocalParameter_epsilon]
  exact S1428ValuationEpsilonOf_ne_zero P c

/-- The compatibility proposition of the constructed cusp clause is the actual
nonvanishing of the local parameter, not `True`. -/
@[simp] theorem S1636CuspClauseOfLocalParameter_compatibility
    (S : SourceSignQuotientData (S1280Arithmetic l))
    (P : S1636CuspLocalParameterFirstMissing l S)
    (c : S1636PaperCusp l S) :
    (S1636CuspClauseOfLocalParameter l S P c).epsilon_compatibility =
      (P.localParameter c ≠ 0) := rfl

theorem S1636CuspClauseOfLocalParameter_epsilon_pos
    (S : SourceSignQuotientData (S1280Arithmetic l))
    (P : S1636CuspLocalParameterFirstMissing l S)
    (c : S1636PaperCusp l S) :
    0 < (S1636CuspClauseOfLocalParameter l S P c).epsilon := by
  rw [S1636CuspClauseOfLocalParameter_epsilon]
  exact S1428ValuationEpsilonOf_pos P c

theorem S1636CuspClauseOfLocalParameter_cuspScale_pos
    (S : SourceSignQuotientData (S1280Arithmetic l))
    (P : S1636CuspLocalParameterFirstMissing l S)
    (c : S1636PaperCusp l S) :
    0 < (S1636CuspClauseOfLocalParameter l S P c).cuspScale := by
  rw [S1636CuspClauseOfLocalParameter_cuspScale]
  exact inv_pos.mpr (S1428ValuationEpsilonOf_pos P c)

/-- The invariant product of the constructed cusp clause is one, exactly as in
the S1428 valuation construction. -/
theorem S1636CuspClauseOfLocalParameter_epsilon_mul_scale
    (S : SourceSignQuotientData (S1280Arithmetic l))
    (P : S1636CuspLocalParameterFirstMissing l S)
    (c : S1636PaperCusp l S) :
    (S1636CuspClauseOfLocalParameter l S P c).epsilon *
      (S1636CuspClauseOfLocalParameter l S P c).cuspScale = 1 := by
  rw [S1636CuspClauseOfLocalParameter_epsilon,
    S1636CuspClauseOfLocalParameter_cuspScale]
  exact S1428ValuationEpsilonOf_mul_scale P c

/-- Contract-level first field of the current `SourceCuspClause`: a real
`epsilon`. -/
abbrev S1636CuspContractFirstField : Type := Real

/-- Contract-level conditional constructor from the first field and its exact
tail.  This is the literal first-field/tail decomposition of the current
record, not an actual cusp coordinate. -/
noncomputable def S1636CuspClauseOfData
    (e : S1636CuspContractFirstField) (t : S1320CuspTail e) :
    SourceCuspClause :=
  S1320CuspClauseOfData e t

/-- The current cusp record is exactly a real first field plus its tail. -/
theorem S1636CuspClause_nonempty_iff_firstField_tail :
    Nonempty SourceCuspClause ↔
      ∃ e : S1636CuspContractFirstField,
        Nonempty (S1320CuspTail e) :=
  S1320CuspClause_nonempty_iff_firstField_tail

/-- The actual q-parameter norm is `1/5`, not a cusp coordinate. -/
theorem S1636ActualQ_eq :
    S1320ActualQ l = (5 : ℝ)⁻¹ :=
  S1320ActualQ_eq l

/-- No cusp clause has `epsilon = log q`: the logarithm of the actual q is
negative while `epsilon` is positive.  This is the formal no-substitution
check for the actual q. -/
theorem S1636ActualQ_ne_cuspEpsilon (C : SourceCuspClause) :
    C.epsilon ≠ Real.log (S1320ActualQ l) :=
  S1330ActualLogQ_ne_epsilon l C

/-! ## 4. Consumer: the S1280 remaining-clause package -/

/-- The three clauses together with the torsion clause form exactly the
`S1280RemainingClauses` package consumed by
`S1280SourceData_of_remaining`. -/
noncomputable def S1636RemainingClauses
    (T : SourceTorsionClause.{0, 0, 0} l)
    (groups : S1636OrbicurveFirstMissing l)
    (G : S1636SectionSupply l)
    (C : SourceCuspClause) : S1280RemainingClauses l where
  torsion := T
  orbicurve := S1636OrbicurveClause l groups
  sections := S1636SectionClause l G
  cusp := C

@[simp] theorem S1636RemainingClauses_orbicurve
    (T : SourceTorsionClause.{0, 0, 0} l)
    (groups : S1636OrbicurveFirstMissing l)
    (G : S1636SectionSupply l)
    (C : SourceCuspClause) :
    (S1636RemainingClauses l T groups G C).orbicurve =
      S1636OrbicurveClause l groups := rfl

@[simp] theorem S1636RemainingClauses_sections
    (T : SourceTorsionClause.{0, 0, 0} l)
    (groups : S1636OrbicurveFirstMissing l)
    (G : S1636SectionSupply l)
    (C : SourceCuspClause) :
    (S1636RemainingClauses l T groups G C).sections =
      S1636SectionClause l G := rfl

@[simp] theorem S1636RemainingClauses_cusp
    (T : SourceTorsionClause.{0, 0, 0} l)
    (groups : S1636OrbicurveFirstMissing l)
    (G : S1636SectionSupply l)
    (C : SourceCuspClause) :
    (S1636RemainingClauses l T groups G C).cusp = C := rfl

/-- The same consumer package with the cusp clause built from the actual S1428
local parameter. -/
noncomputable def S1636RemainingClausesOfLocalParameter
    (T : SourceTorsionClause.{0, 0, 0} l)
    (groups : S1636OrbicurveFirstMissing l)
    (G : S1636SectionSupply l)
    (S : SourceSignQuotientData (S1280Arithmetic l))
    (P : S1636CuspLocalParameterFirstMissing l S)
    (c : S1636PaperCusp l S) : S1280RemainingClauses l :=
  S1636RemainingClauses l T groups G
    (S1636CuspClauseOfLocalParameter l S P c)

@[simp] theorem S1636RemainingClausesOfLocalParameter_cusp
    (T : SourceTorsionClause.{0, 0, 0} l)
    (groups : S1636OrbicurveFirstMissing l)
    (G : S1636SectionSupply l)
    (S : SourceSignQuotientData (S1280Arithmetic l))
    (P : S1636CuspLocalParameterFirstMissing l S)
    (c : S1636PaperCusp l S) :
    (S1636RemainingClausesOfLocalParameter l T groups G S P c).cusp =
      S1636CuspClauseOfLocalParameter l S P c := rfl

/-- The five D9 compatibility pairs are the remaining input of
`SourceDefinition31Data`; they are not constructed in this file.  This is the
exact interface of `S1280SourceData_of_remaining`. -/
structure S1636D9Compatibility where
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

/-- **The literal `SourceDefinition31Data` assembly.**  The arithmetic, selected
places, bad places and reduction are the actual S1280 fields; the orbicurve,
section and cusp fields are the clauses constructed in this file; the five
remaining D9 compatibility pairs are supplied as explicit input. -/
noncomputable def S1636SourceData
    (T : SourceTorsionClause.{0, 0, 0} l)
    (groups : S1636OrbicurveFirstMissing l)
    (G : S1636SectionSupply l)
    (C : SourceCuspClause)
    (K : S1636D9Compatibility) : SourceDefinition31Data l :=
  S1280SourceData_of_remaining l (S1636RemainingClauses l T groups G C)
    K.redCompat K.redCompat_proved K.torCompat K.torCompat_proved
    K.orbCompat K.orbCompat_proved K.secCompat K.secCompat_proved
    K.cusCompat K.cusCompat_proved

@[simp] theorem S1636SourceData_orbicurve
    (T : SourceTorsionClause.{0, 0, 0} l)
    (groups : S1636OrbicurveFirstMissing l)
    (G : S1636SectionSupply l)
    (C : SourceCuspClause)
    (K : S1636D9Compatibility) :
    (S1636SourceData l T groups G C K).orbicurve =
      S1636OrbicurveClause l groups := rfl

@[simp] theorem S1636SourceData_sections
    (T : SourceTorsionClause.{0, 0, 0} l)
    (groups : S1636OrbicurveFirstMissing l)
    (G : S1636SectionSupply l)
    (C : SourceCuspClause)
    (K : S1636D9Compatibility) :
    (S1636SourceData l T groups G C K).sections =
      S1636SectionClause l G := rfl

@[simp] theorem S1636SourceData_cusp
    (T : SourceTorsionClause.{0, 0, 0} l)
    (groups : S1636OrbicurveFirstMissing l)
    (G : S1636SectionSupply l)
    (C : SourceCuspClause)
    (K : S1636D9Compatibility) :
    (S1636SourceData l T groups G C K).cusp = C := rfl

/-! ## 5. Axiom footprint -/

#print axioms S1636OrbicurveClause
#print axioms S1636SectionClause
#print axioms S1636CuspClauseOfRealCuspCoordinate
#print axioms S1636CuspClauseOfLocalParameter
#print axioms S1636CuspClauseOfLocalParameter_epsilon_mul_scale
#print axioms S1636ActualQ_ne_cuspEpsilon
#print axioms S1636RemainingClauses
#print axioms S1636RemainingClausesOfLocalParameter
#print axioms S1636SourceData

end LeanFormal.IUT.XiFPaper.S1636SourceClausesActual

end
