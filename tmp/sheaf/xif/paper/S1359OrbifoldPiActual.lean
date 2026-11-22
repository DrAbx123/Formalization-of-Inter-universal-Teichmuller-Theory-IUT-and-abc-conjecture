import tmp.sheaf.xif.paper.S1319OrbicurveClauseActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36OrbicurveFeasibility
import LeanFormal.IUT.IUTI.HodgeTheater.SourceClauseAssemblyUnitsReduction
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31OrbicurveInstance

/-!
# S1359: the actual orbifold-Pi slot of S1319, or its exact first field

S1319 constructs the actual point-level D6 boundary clause from the concrete
Gaussian curve and freezes the stack/fundamental-group gap as
S1319OrbifoldPiData l, consisting of a hyperbolic orbicurve X over the S1280
Gaussian field K, a proof that X is nonterminal (not a point fiber), the
once-punctured-elliptic signature equation, and the certified
OrbicurveFundamentalGroupData of X over the absolute Galois group.

This file extracts the exact content of that frozen structure.

## What is proved

* S1319OrbifoldPiData l is equivalent to a sigma type consisting of the
  first field S1359FirstField l and the residual group data
  OrbicurveFundamentalGroupData F.X galois.  The first field and the residual
  field are separated exactly; no field is dropped and no surrogate is
  inserted.

* S1359FirstField l is the literal non-group prefix of the frozen structure:
  an actual HyperbolicOrbicurve over K, with the nonterminal condition and the
  once-punctured-elliptic signature.

* S1359FirstField l is nonempty exactly when a non-point etale stack fiber
  over K exists (S1359StackFirstField l): a fiber, its effective-descent
  proof, and a proof that it is not a point fiber.  This is the precise D6
  stack content.

* From the exact missing D6 object MissingD6GeometricRealization K of
  Example36OrbicurveFeasibility, the first field is constructed:
  S1359FirstFieldOfMissingD6.  Its stack fiber is definitionally the supplied
  D6 fiber, its signature is definitionally once-punctured elliptic, and its
  nonterminal proof is extracted from the D6 nondegeneracy proof.  Hence,
  from a D6 realization plus actual OrbicurveFundamentalGroupData, the full
  S1319OrbifoldPiData is constructed (S1359OrbifoldPiDataOfMissingD6).

* Negative controls: every S1319OrbifoldPiData is non-point, cannot use the
  terminal constant stack, and cannot use the point-fiber
  degeneratePointFiberOrbicurve.  The point-fiber signature insertion of
  Example36 fails the nonterminal condition exactly.

* The orbifold Pi exact sequence is built from the residual group data, not
  from the l-torsion sequence of S1319.  The l-torsion sequence is recorded as
  such but is never used to fill the groups field.

## Exact boundary

The tree contains no inhabitant of MissingD6GeometricRealization K
(Example36OrbicurveFeasibility proves that the point/terminal fibers fail it
and records that no actual non-point etale stack fiber is constructed), and no
inhabitant of OrbicurveEtaleFundamentalGroup for any orbicurve.  Hence this
file does not assert Nonempty (S1319OrbifoldPiData l).  It constructs the first
field from the exact D6 realization, and the full data from the D6 realization
and the group data.  Those two inputs are the exact remaining fields; neither
is replaced by a point fiber, a terminal stack, an arbitrary carrier, the
l-torsion sequence, an axiom or sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1359OrbifoldPiActual

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1319OrbicurveClauseActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility

/-- The S1280 Gaussian field K over which the S1319 D6 clause lives. -/
abbrev S1359K (l : PrimeGeFive) : Type := (S1280Arithmetic l).K

/-- The absolute Galois group used by the frozen S1319 orbifold-Pi slot. -/
abbrev S1359Galois (l : PrimeGeFive) : ProfiniteGrp :=
  Iut.AbsoluteGaloisProfinite (S1359K l)

/-- The literal first field type of S1319OrbifoldPiData: a hyperbolic
orbicurve over the S1280 Gaussian field. -/
abbrev S1359LiteralFirstField (l : PrimeGeFive) : Type 1 :=
  Iut.HyperbolicOrbicurve (S1359K l)

/-- S1319NonterminalFiber is the classical negation of IsPointFiber: a stack
fiber is nonterminal iff it is not a point fiber at every test scheme. -/
theorem S1359NonterminalFiber_iff_notPointFiber (l : PrimeGeFive)
    (X : Iut.HyperbolicOrbicurve (S1359K l)) :
    S1319NonterminalFiber X ↔ ¬ IsPointFiber X.stack.fiber := by
  classical
  constructor
  · rintro ⟨U, hU⟩ h
    exact hU (h U)
  · intro h
    by_contra h'
    apply h
    intro U
    by_contra hU
    exact h' ⟨U, hU⟩

/-- Exact non-group prefix of S1319OrbifoldPiData: an actual hyperbolic
orbicurve over K, together with the two remaining non-group fields. -/
structure S1359FirstField (l : PrimeGeFive) where
  /-- The literal first field of the frozen S1319 structure. -/
  X : Iut.HyperbolicOrbicurve (S1359K l)
  /-- The first field is not a point/terminal fiber. -/
  nonterminal : S1319NonterminalFiber X
  /-- Its signature is exactly the once-punctured elliptic one. -/
  signature : X.signature = Iut.OrbicurveSignature.oncePuncturedElliptic

/-- The exact residual field after the first field: the certified arithmetic /
geometric orbifold fundamental-group data over the absolute Galois group. -/
abbrev S1359OrbifoldPiRemainder (l : PrimeGeFive) (F : S1359FirstField l) : Type 1 :=
  Iut.OrbicurveFundamentalGroupData F.X (S1359Galois l)

/-- The exact stack content of the first field: a non-point etale stack fiber
with effective descent. -/
structure S1359StackFirstField (l : PrimeGeFive) where
  fiber : Iut.EtaleStackPseudofunctor (S1359K l)
  isStack : fiber.IsStack (Iut.SchemeOverField.etaleTopology (S1359K l))
  nonPoint : ¬ IsPointFiber fiber

/-- From a non-point etale stack fiber, construct the first field with the
once-punctured elliptic signature.  The signature certificate is inserted by
realizedHyperbolicOrbicurve; the nontrivial content is the non-point fiber. -/
noncomputable def S1359FirstFieldOfFiber (l : PrimeGeFive)
    (fiber : Iut.EtaleStackPseudofunctor (S1359K l))
    (isStack : fiber.IsStack (Iut.SchemeOverField.etaleTopology (S1359K l)))
    (h : ¬ IsPointFiber fiber) :
    S1359FirstField l := by
  classical
  refine
    { X := realizedHyperbolicOrbicurve (S1359K l) fiber isStack
        Iut.OrbicurveSignature.oncePuncturedElliptic
        Iut.OrbicurveSignature.oncePuncturedElliptic_isHyperbolic
      nonterminal := ?_
      signature := rfl }
  change ∃ U : (Iut.SchemeOverField (S1359K l))ᵒᵖ,
    ¬ Subsingleton (fiber.obj (LocallyDiscrete.mk U))
  by_contra h'
  apply h
  intro U
  by_contra hU
  exact h' ⟨U, hU⟩

noncomputable def S1359StackFirstFieldOfFirstField (l : PrimeGeFive)
    (F : S1359FirstField l) : S1359StackFirstField l where
  fiber := F.X.stack.fiber
  isStack := F.X.stack.isStack
  nonPoint := (S1359NonterminalFiber_iff_notPointFiber l F.X).mp F.nonterminal

noncomputable def S1359FirstFieldOfStackFirstField (l : PrimeGeFive)
    (S : S1359StackFirstField l) : S1359FirstField l :=
  S1359FirstFieldOfFiber l S.fiber S.isStack S.nonPoint

theorem S1359FirstField_nonempty_iff_stackFirstField (l : PrimeGeFive) :
    Nonempty (S1359FirstField l) ↔ Nonempty (S1359StackFirstField l) := by
  constructor
  · rintro ⟨F⟩
    exact ⟨S1359StackFirstFieldOfFirstField l F⟩
  · rintro ⟨S⟩
    exact ⟨S1359FirstFieldOfStackFirstField l S⟩

noncomputable def S1359FirstFieldOfMissingD6 (l : PrimeGeFive)
    (D : MissingD6GeometricRealization (S1359K l)) : S1359FirstField l :=
  S1359FirstFieldOfFiber l D.fiber D.isStack D.nondegenerate

@[simp] theorem S1359FirstFieldOfMissingD6_fiber (l : PrimeGeFive)
    (D : MissingD6GeometricRealization (S1359K l)) :
    (S1359FirstFieldOfMissingD6 l D).X.stack.fiber = D.fiber := rfl

@[simp] theorem S1359FirstFieldOfMissingD6_signature (l : PrimeGeFive)
    (D : MissingD6GeometricRealization (S1359K l)) :
    (S1359FirstFieldOfMissingD6 l D).X.signature =
      Iut.OrbicurveSignature.oncePuncturedElliptic := rfl

theorem S1359FirstFieldOfMissingD6_nonterminal (l : PrimeGeFive)
    (D : MissingD6GeometricRealization (S1359K l)) :
    S1319NonterminalFiber (S1359FirstFieldOfMissingD6 l D).X :=
  (S1359FirstFieldOfMissingD6 l D).nonterminal

noncomputable def S1359OrbifoldPiDataOf (l : PrimeGeFive) (F : S1359FirstField l)
    (groups : S1359OrbifoldPiRemainder l F) :
    S1319OrbifoldPiData l where
  X := F.X
  nonterminal := F.nonterminal
  signature := F.signature
  groups := groups

@[simp] theorem S1359OrbifoldPiDataOf_X (l : PrimeGeFive)
    (F : S1359FirstField l) (groups : S1359OrbifoldPiRemainder l F) :
    (S1359OrbifoldPiDataOf l F groups).X = F.X := rfl

@[simp] theorem S1359OrbifoldPiDataOf_groups (l : PrimeGeFive)
    (F : S1359FirstField l) (groups : S1359OrbifoldPiRemainder l F) :
    (S1359OrbifoldPiDataOf l F groups).groups = groups := rfl

noncomputable def S1359OrbifoldPiDataOfMissingD6 (l : PrimeGeFive)
    (D : MissingD6GeometricRealization (S1359K l))
    (groups : S1359OrbifoldPiRemainder l (S1359FirstFieldOfMissingD6 l D)) :
    S1319OrbifoldPiData l :=
  S1359OrbifoldPiDataOf l (S1359FirstFieldOfMissingD6 l D) groups

@[simp] theorem S1359OrbifoldPiDataOfMissingD6_X (l : PrimeGeFive)
    (D : MissingD6GeometricRealization (S1359K l))
    (groups : S1359OrbifoldPiRemainder l (S1359FirstFieldOfMissingD6 l D)) :
    (S1359OrbifoldPiDataOfMissingD6 l D groups).X =
      (S1359FirstFieldOfMissingD6 l D).X := rfl

def S1359FirstFieldOfData (l : PrimeGeFive) (D : S1319OrbifoldPiData l) :
    S1359FirstField l where
  X := D.X
  nonterminal := D.nonterminal
  signature := D.signature

def S1359GroupsOfData (l : PrimeGeFive) (D : S1319OrbifoldPiData l) :
    S1359OrbifoldPiRemainder l (S1359FirstFieldOfData l D) :=
  D.groups

noncomputable def S1359OrbifoldPiDataEquiv (l : PrimeGeFive) :
    S1319OrbifoldPiData l ≃
      (Σ F : S1359FirstField l, S1359OrbifoldPiRemainder l F) where
  toFun D := ⟨S1359FirstFieldOfData l D, D.groups⟩
  invFun P := S1359OrbifoldPiDataOf l P.1 P.2
  left_inv D := by
    cases D
    rfl
  right_inv P := by
    rcases P with ⟨⟨X, nonterminal, signature⟩, groups⟩
    rfl

theorem S1359OrbifoldPiGap_iff (l : PrimeGeFive) :
    S1319OrbifoldPiGap l ↔
      ∃ F : S1359FirstField l, Nonempty (S1359OrbifoldPiRemainder l F) := by
  rw [S1319OrbifoldPiGap]
  constructor
  · rintro ⟨D⟩
    exact ⟨S1359FirstFieldOfData l D, ⟨D.groups⟩⟩
  · rintro ⟨F, ⟨groups⟩⟩
    exact ⟨S1359OrbifoldPiDataOf l F groups⟩

theorem S1359FirstField_not_pointFiber (l : PrimeGeFive) (F : S1359FirstField l) :
    ¬ IsPointFiber F.X.stack.fiber :=
  (S1359NonterminalFiber_iff_notPointFiber l F.X).mp F.nonterminal

theorem S1359OrbifoldPiData_not_pointFiber (l : PrimeGeFive)
    (D : S1319OrbifoldPiData l) :
    ¬ IsPointFiber D.X.stack.fiber :=
  (S1359NonterminalFiber_iff_notPointFiber l D.X).mp D.nonterminal

theorem S1359OrbifoldPiData_not_terminal (l : PrimeGeFive)
    (D : S1319OrbifoldPiData l) :
    D.X.stack ≠ Definition31OrbicurveInstance.terminalConstantEtaleStack (S1359K l) := by
  intro h
  exact Definition31OrbicurveInstance.terminalConstantEtaleStack_not_hyperbolicOrbicurve_carrier
    (S1359K l) D.X h

theorem S1359OrbifoldPiData_X_ne_degeneratePointFiber (l : PrimeGeFive)
    (D : S1319OrbifoldPiData l) :
    D.X ≠ degeneratePointFiberOrbicurve (S1359K l) := by
  intro h
  apply S1359OrbifoldPiData_not_pointFiber l D
  rw [h]
  exact degeneratePointFiberOrbicurve_isPointFiber (S1359K l)

theorem S1359Nonterminal_degeneratePointFiber (l : PrimeGeFive) :
    ¬ S1319NonterminalFiber (degeneratePointFiberOrbicurve (S1359K l)) := by
  intro h
  exact S1359FirstField_not_pointFiber l
    { X := degeneratePointFiberOrbicurve (S1359K l)
      nonterminal := h
      signature := degeneratePointFiberOrbicurve_signature (S1359K l) } (by
        rw [degeneratePointFiberOrbicurve_stack_fiber]
        exact sourceStackPoint_isPointFiber (S1359K l))

theorem S1359NoTerminalCarrier (l : PrimeGeFive) :
    ¬ ∃ X : Iut.HyperbolicOrbicurve (S1359K l),
      X.stack = Definition31OrbicurveInstance.terminalConstantEtaleStack (S1359K l) := by
  rintro ⟨X, h⟩
  exact Definition31OrbicurveInstance.terminalConstantEtaleStack_not_hyperbolicOrbicurve_carrier
    (S1359K l) X h

theorem S1359SourceClause_exactSequence_is_lTorsion (l : PrimeGeFive) :
    (S1319SourceOrbicurveClause l).exactSequence =
      S1319LTorsionExactSequence l := rfl

@[simp] theorem S1359LTorsionSequence_baseGroup (l : PrimeGeFive) :
    (S1319LTorsionExactSequence l).baseGroup =
      (S1319LTorsionRepresentation l).range := rfl

noncomputable def S1359OrbifoldPiSequence (l : PrimeGeFive) (D : S1319OrbifoldPiData l) :
    Iut.ProfiniteFundamentalExactSequence
      D.groups.geometric.group D.groups.arithmetic.group (S1359Galois l) :=
  Iut.OrbicurveFundamentalGroupData.exactSequence D.groups

theorem S1359OrbifoldPiSequence_is_from_groups (l : PrimeGeFive)
    (D : S1319OrbifoldPiData l) :
    S1359OrbifoldPiSequence l D =
      Iut.OrbicurveFundamentalGroupData.exactSequence D.groups := rfl

@[simp] theorem S1359OrbifoldPiSequence_projection (l : PrimeGeFive)
    (D : S1319OrbifoldPiData l) :
    (S1359OrbifoldPiSequence l D).projection = D.groups.projection := rfl

@[simp] theorem S1359OrbifoldPiSequence_inclusion (l : PrimeGeFive)
    (D : S1319OrbifoldPiData l) :
    (S1359OrbifoldPiSequence l D).inclusion =
      (Iut.closedSubgroupProfiniteInclusion
        (Iut.profiniteKernelClosedSubgroup D.groups.projection)).hom := rfl

/-! ## 6. Axiom footprint -/

#print axioms S1359NonterminalFiber_iff_notPointFiber
#print axioms S1359FirstFieldOfFiber
#print axioms S1359FirstField_nonempty_iff_stackFirstField
#print axioms S1359FirstFieldOfMissingD6
#print axioms S1359OrbifoldPiDataOfMissingD6
#print axioms S1359OrbifoldPiDataEquiv
#print axioms S1359OrbifoldPiGap_iff
#print axioms S1359OrbifoldPiData_not_pointFiber
#print axioms S1359OrbifoldPiData_not_terminal
#print axioms S1359OrbifoldPiData_X_ne_degeneratePointFiber
#print axioms S1359Nonterminal_degeneratePointFiber
#print axioms S1359OrbifoldPiSequence

end LeanFormal.IUT.XiFPaper.S1359OrbifoldPiActual

end
