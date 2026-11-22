import tmp.sheaf.n8.closure.NativeSourceOrbicurveActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourceClauseConstructors
import Mathlib.Tactic

/-!
# Deep attempt: cuspCount/positivity and exact-sequence splitting

Clause F supplies a single cusp origin and a cuspidal decomposition, but
NOT a finite cusp set or a cardinality. Clause E supplies local exact
sequence embeddings, but NOT a splitting homomorphism of the global exact
sequence. This file states the two exact source primitives and proves the
conditional constructions from them. No value or splitting is fabricated.

Proved unconditional: curveCompatibility from the actual finite-etale cover
D.k_l_torsion_cover; the equivalence between the splitting primitive and a
supplied split exact sequence; and the cusp-count construction from an exact
finite cusp set containing S.epsilon.

No lake/compile is run in this task.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.InitialThetaSource.NativeOrbicurveCountProof

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open Iut

universe u

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
variable {S : SourceSignQuotientData A} {C : SourceClauseA A S}
variable {B : SourceClauseB A S C} {Dc : SourceClauseC A S C B}

/-- Exact source primitive for cuspCount: a finite cusp set over the actual
cK orbicurve containing the clause-F cusp origin S.epsilon. No cardinality
is available without this finite set. -/
def CuspCountSourceData (S : SourceSignQuotientData A) : Prop :=
  ∃ cusps : Finset (Iut.OrbicurveBoundaryCusp S.cK),
    0 < cusps.card ∧ S.epsilon ∈ cusps

/-- The cusp count constructed from an exact finite cusp set. -/
def cuspCountOfSource (h : CuspCountSourceData S) : Nat :=
  h.choose.card

theorem cuspCountOfSource_pos (h : CuspCountSourceData S) :
    0 < cuspCountOfSource h :=
  h.choose_spec.1

theorem cuspCountOfSource_epsilon_mem (h : CuspCountSourceData S) :
    S.epsilon ∈ h.choose :=
  h.choose_spec.2

/-- Exact source primitive for the exact-sequence splitting: a group
homomorphism from the absolute Galois group to the x-arithmetic group
whose composite with the actual projection is the identity. Clause D/E
do not supply this section. -/
def ExactSequenceSplittingPrimitive
    (E : SourceClauseD A S C B Dc) : Prop :=
  ∃ sectionMap : ↥(AbsoluteGaloisProfinite A.K) →*
      ↥E.x_groups.sequence.arithmetic,
    ∀ x : ↥(AbsoluteGaloisProfinite A.K),
      E.x_groups.sequence.projection (sectionMap x) = x

/-- The conditional construction of the actual source exact-sequence clause
from the exact splitting primitive. -/
def nativeExactSequence_of_splitting
    (E : SourceClauseD A S C B Dc)
    (h : ExactSequenceSplittingPrimitive E) :
    SourceExactSequenceClause := by
  classical
  let sectionMap := Classical.choose h
  exact NativeSourceOrbicurveActual.sourceExactSequenceOfGroups
    E.x_groups.sequence sectionMap (Classical.choose_spec h)

/-- Splitting primitive is exactly the input needed by the native exact
sequence constructor. -/
theorem exactSequenceSplittingPrimitive_iff
    (E : SourceClauseD A S C B Dc) :
    ExactSequenceSplittingPrimitive E ↔
      ∃ (sectionMap : ↥(AbsoluteGaloisProfinite A.K) →*
          ↥E.x_groups.sequence.arithmetic),
        ∀ x : ↥(AbsoluteGaloisProfinite A.K),
          E.x_groups.sequence.projection (sectionMap x) = x := by
  rfl

/-- Unconditional curve compatibility from clause D. -/
theorem curveCompatibility_of_clauseD
    (E : SourceClauseD A S C B Dc) :
    Nonempty (SourceOrbicurveFiniteEtaleCover S.xK S.cK) :=
  ⟨E.k_l_torsion_cover⟩

/- Exact missing source theorems:
1. CuspCountSourceData S: a finite cusp set over S.cK containing S.epsilon.
   Clause F supplies one cusp origin and a cuspidal decomposition, not a
   finite cusp set/cardinality; no Nat is fabricated.
2. ExactSequenceSplittingPrimitive E: a splitting sectionMap/right-inverse.
   Clause E supplies local embeddings of the global exact sequence, not a
   global splitting homomorphism; no section is fabricated.
The conditional constructions above are the exact reductions. -/

#check CuspCountSourceData
#check cuspCountOfSource
#check ExactSequenceSplittingPrimitive
#check nativeExactSequence_of_splitting
#check curveCompatibility_of_clauseD

end LeanFormal.IUT.InitialThetaSource.NativeOrbicurveCountProof

end
