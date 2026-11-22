import LeanFormal.IUT.IUTIII.Theorem311.Output.MultiradialAlgorithmReduction
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionRecordExistenceGeneral
import Mathlib.Tactic

/-!
  # General route normal form for the multiradial algorithm (Theorem 3.11, (i))

  `MultiradialAlgorithmReduction.lean` reduced `IUT-III.multiradial-algorithm`
  to the carrier-level algorithm contract plus two residual cards:

  * (1) the carrier instance from the actual IUT I-II data (connector and
    level-additivity);
  * (2) the general route normal form beyond the finite Q(i)-at-5 carrier.

  This file closes card (2) and advances the algorithm-level invariant
  calculus, using the generic normalization proved in
  `SourceProcessionRecordExistenceGeneral.lean`:

  * `routeNormalForm_general`: the frozen predicate
    `MultiradialAlgorithmReduction.RouteNormalForm` holds for every
    parameterized carrier - the residual card (2) of the reduction record;
  * `routeTarget_ind3_budget_unique` and `routeTarget_normal_form_iff`: any
    decomposition of a route target into an Ind3 iterate of a same-level
    choice has a *uniquely determined* vertical budget, equal to the route's
    `verticalBudget`; the normalized decomposition is the fixed-budget one;
  * `horizontalSteps_idempotent` and `routeTarget_horizontalSteps_stable`:
    normalization is idempotent, at the route level and at the output level;
  * `routeTarget_horizontalSteps_quotient`: the normalized output lies in
    the input's (Ind1)/(Ind2) quotient class - the algorithm-level quotient
    invariant over an arbitrary route;
  * `runAlgorithm_target_ind3_normal_form` and
    `runAlgorithm_target_normalized_decomposition`: the same statements at
    the `runAlgorithm` interface.

  Paper: IUT III, Theorem 3.11, (i) (the algorithm in the procession of
  D-prime-strips, functorial in the processions; [IUTchI], Proposition 6.9,
  (ii)), with the indeterminacies (Ind1)/(Ind2) rendered as the quotient
  class and (Ind3) as the log-link iterate.  Card (1), the carrier instance
  from the actual IUT I-II data, is not touched here.
-/

namespace LeanFormal.IUT

noncomputable section

namespace MultiradialAlgorithmGeneral

open MultiradialKernel
open MultiradialKernel.Core
open ParametricTheorem311
open SourceProcessionBoundary

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label]

/-! ## 1. Idempotence and stability of horizontal normalization -/

/- Dropping the Ind3 steps is idempotent: a route is already horizontal
    after one pass of `horizontalSteps`. -/
omit [AddGroup Label] in
theorem horizontalSteps_idempotent (route : List (RouteStep Label)) :
    horizontalSteps (horizontalSteps route) = horizontalSteps route := by
  induction route with
  | nil => rfl
  | cons step rest ih =>
      cases step <;> simp [horizontalSteps, ih]

/- Every step of `horizontalSteps route` is horizontal. -/
omit [AddGroup Label] in
theorem horizontalSteps_isHorizontal (route : List (RouteStep Label)) :
    ∀ step ∈ horizontalSteps route, horizontal step := by
  induction route with
  | nil => simp [horizontalSteps]
  | cons step rest ih =>
      cases step with
      | ind1 g =>
          intro s hs
          simp only [horizontalSteps, List.mem_cons] at hs
          rcases hs with rfl | hs
          · exact horizontal_of_ind1 g
          · exact ih s hs
      | ind2 g =>
          intro s hs
          simp only [horizontalSteps, List.mem_cons] at hs
          rcases hs with rfl | hs
          · exact horizontal_of_ind2 g
          · exact ih s hs
      | ind3 n =>
          simpa only [horizontalSteps] using ih

/-- Output-level stability: re-normalizing the horizontal part does not
    change the normalized output. -/
theorem routeTarget_horizontalSteps_stable (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) :
    routeTarget carrier (horizontalSteps route) c =
      routeTarget carrier (horizontalSteps (horizontalSteps route)) c := by
  rw [horizontalSteps_idempotent route]

/-- The normalized output lies in the (Ind1)/(Ind2) quotient class of the
    input: over an arbitrary route, horizontal normalization composes with
    the generated-equality quotient map. -/
theorem routeTarget_horizontalSteps_quotient (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) :
    carrier.core.generatedQuotientMap
        (routeTarget carrier (horizontalSteps route) c) =
      carrier.core.generatedQuotientMap c := by
  exact (carrier.core.generatedQuotientMap_eq_of_generated
    (generated_of_horizontal_route carrier.core (horizontalSteps route)
      (horizontalSteps_isHorizontal route) c)).symm

/-! ## 2. Uniqueness of the vertical budget and the normalized form -/

/-- The vertical budget of a normalized decomposition is unique: whenever a
    route target equals an Ind3 iterate of a choice at the route's own
    level, the iterate count is exactly the route's `verticalBudget`.
    Equivalently, the vertical budget of the algorithm is independent of the
    decomposition chosen. -/
theorem routeTarget_ind3_budget_unique (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c b : Choice) (n : Nat)
    (hdecomp : routeTarget carrier route c = carrier.core.ind3 n b)
    (hlevel : carrier.core.level b = carrier.core.level c) :
    n = verticalBudget route := by
  have hbudget := routeTarget_level_eq_budget carrier route c
  rw [hdecomp, carrier.ind3_level_eq, hlevel] at hbudget
  exact Nat.add_left_cancel hbudget

/-- The normalized decomposition: a route target is an Ind3 iterate with the
    fixed budget `verticalBudget route` of a same-level choice. -/
theorem routeTarget_normalized_decomposition (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) :
    ∃ b, carrier.core.level b = carrier.core.level c ∧
      routeTarget carrier route c =
        carrier.core.ind3 (verticalBudget route) b := by
  refine ⟨routeTarget carrier (horizontalSteps route) c, ?_, ?_⟩
  · rw [routeTarget_level_eq_budget, verticalBudget_horizontalSteps,
      Nat.add_zero]
  · exact routeTarget_normalize carrier route c

/-- Characterization of the normal form: decompositions of the route target
    into an Ind3 iterate of a same-level choice exist if and only if they
    exist with the fixed budget `verticalBudget route`. -/
theorem routeTarget_normal_form_iff (carrier : Carrier Label Choice)
    (route : List (RouteStep Label)) (c : Choice) :
    (∃ b n, carrier.core.level b = carrier.core.level c ∧
        routeTarget carrier route c = carrier.core.ind3 n b) ↔
      ∃ b, carrier.core.level b = carrier.core.level c ∧
        routeTarget carrier route c =
          carrier.core.ind3 (verticalBudget route) b := by
  constructor
  · rintro ⟨b, n, hlevel, hdecomp⟩
    have hbudget := routeTarget_ind3_budget_unique carrier route c b n
      hdecomp hlevel
    exact ⟨b, hlevel, by rw [hdecomp, hbudget]⟩
  · rintro ⟨b, hlevel, hdecomp⟩
    exact ⟨b, verticalBudget route, hlevel, hdecomp⟩

/-! ## 3. The statements at the `runAlgorithm` interface -/

/-- The output of `runAlgorithm` satisfies the Ind3 normal form relative to
    the algorithm input. -/
theorem runAlgorithm_target_ind3_normal_form (carrier : Carrier Label Choice)
    (input : AlgorithmInput carrier) :
    ∃ b n, carrier.core.level b = carrier.core.level input.source ∧
      (runAlgorithm carrier input).target = carrier.core.ind3 n b := by
  rw [runAlgorithm_target]
  exact routeTarget_ind3_normal_form carrier input.route input.source

/-- The output of `runAlgorithm` has the normalized decomposition with the
    fixed budget `verticalBudget input.route`. -/
theorem runAlgorithm_target_normalized_decomposition
    (carrier : Carrier Label Choice) (input : AlgorithmInput carrier) :
    ∃ b, carrier.core.level b = carrier.core.level input.source ∧
      (runAlgorithm carrier input).target =
        carrier.core.ind3 (verticalBudget input.route) b := by
  rw [runAlgorithm_target]
  exact routeTarget_normalized_decomposition carrier input.route input.source

/-! ## 4. Closing residual card (2) of the algorithm reduction -/

/-- The frozen route-normal-form predicate of the multiradial algorithm
    reduction holds for every parameterized carrier: residual card (2) of
    `MultiradialAlgorithmReduction.multiradialAlgorithmReductionRecord`
    ("general route normal form beyond the finite carrier") is closed. -/
theorem routeNormalForm_general (carrier : Carrier Label Choice) :
    MultiradialAlgorithmReduction.RouteNormalForm carrier :=
  route_normal_form_holds carrier

end MultiradialAlgorithmGeneral

end

end LeanFormal.IUT
namespace LeanFormal.IUT.Audit

def multiradialAlgorithmGeneralRouteNormalForm : Obligation :=
  { id := "IUT-III.multiradial-algorithm.general-route-normal-form"
    source :=
      "IUT III, Theorem 3.11, (i) (algorithm in the procession of " ++
        "D-prime-strips); [IUTchI], Proposition 6.9, (ii) (corpus I.txt:9811)"
    status := VerificationStatus.conditional
    note :=
      "The general route normal form card of `IUT-III.multiradial-algorithm` " ++
        "(card (2) of the reduction record in MultiradialAlgorithmReduction) " ++
        "is closed: `routeNormalForm_general` proves the frozen predicate " ++
        "`RouteNormalForm` for every parameterized carrier, via the generic " ++
        "normalization of SourceProcessionRecordExistenceGeneral " ++
        "(`routeTarget_normalize`, `routeTarget_ind3_normal_form`). " ++
        "Algorithm-level invariants are proved generically: the vertical " ++
        "budget of any normalized decomposition is unique " ++
        "(`routeTarget_ind3_budget_unique`), the normalized decomposition " ++
        "has the fixed-budget form (`routeTarget_normal_form_iff`), " ++
        "normalization is idempotent and stable " ++
        "(`horizontalSteps_idempotent`, `routeTarget_horizontalSteps_stable`), " ++
        "and the normalized output lies in the input's (Ind1)/(Ind2) " ++
        "quotient class (`routeTarget_horizontalSteps_quotient`); the " ++
        "statements hold at the `runAlgorithm` interface " ++
        "(`runAlgorithm_target_ind3_normal_form`, " ++
        "`runAlgorithm_target_normalized_decomposition`). The remaining " ++
        "card of the algorithm obligation is card (1): the carrier " ++
        "instance from the actual IUT I-II data (connector and " ++
        "level-additivity), which is not constructed here."
    dependsOn :=
      [ "IUT-III.multiradial-algorithm",
        "IUT-III.source-procession-record-existence-general",
        "IUT-III.concrete-source-multiradial-kernel" ] }

end LeanFormal.IUT.Audit
