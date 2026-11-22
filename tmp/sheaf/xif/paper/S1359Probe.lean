import tmp.sheaf.xif.paper.S1319OrbicurveClauseActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36OrbicurveFeasibility
import LeanFormal.IUT.IUTI.HodgeTheater.SourceClauseAssemblyUnitsReduction
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31OrbicurveInstance

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

abbrev S1359K (l : PrimeGeFive) : Type := (S1280Arithmetic l).K

abbrev S1359Galois (l : PrimeGeFive) : ProfiniteGrp :=
  Iut.AbsoluteGaloisProfinite (S1359K l)

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

structure S1359FirstField (l : PrimeGeFive) where
  X : Iut.HyperbolicOrbicurve (S1359K l)
  nonterminal : S1319NonterminalFiber X
  signature : X.signature = Iut.OrbicurveSignature.oncePuncturedElliptic

abbrev S1359OrbifoldPiRemainder (l : PrimeGeFive) (F : S1359FirstField l) : Type 1 :=
  Iut.OrbicurveFundamentalGroupData F.X (S1359Galois l)

structure S1359StackFirstField (l : PrimeGeFive) where
  fiber : Iut.EtaleStackPseudofunctor (S1359K l)
  isStack : fiber.IsStack (Iut.SchemeOverField.etaleTopology (S1359K l))
  nonPoint : ¬ IsPointFiber fiber

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

end LeanFormal.IUT.XiFPaper.S1359OrbifoldPiActual

end
