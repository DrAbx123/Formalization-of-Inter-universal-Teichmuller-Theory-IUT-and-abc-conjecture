/-
# S1751: finite-index subgroups of an absolute Galois group need not be open

## Question

S1737 reduced the literal full-action statement

  'PreGaloisCategory.IsFundamentalGroup (Action.forget FintypeCat G) G'

to

  'S1737EveryFiniteIndexSubgroupOpen G'

(every finite-index subgroup of 'G' is open), and proved the finite case.
The question here is whether this holds for 'G = Iut.AbsoluteGaloisProfinite F',
in particular for the actual IUT field 'F = S1720Field'.

## Answer

It does **not** hold.  The proposition is false for every number field, hence
in particular for 'F = S1720Field' (which is a number field,
'S1720NumberField').  This is not a missing Mathlib theorem: the statement is
false, so no proof can exist.  The literal full-action statement is therefore
false at the actual field, and the correct replacement is the category of
finite *continuous* 'G'-sets, 'ContAction FintypeCat G', exactly the S1737
'S1737ContinuousEtaleFundamentalGroup' construction.

### The counterexample (published)

J. S. Milne, *Fields and Galois Theory*, Chapter 7, Proposition 7.29:
'Gal(Qbar/Q)' has non-open **normal** subgroups of index '2 ^ n' for every
'n > 1'.  The construction is:

* Let 'E = Q(i, sqrt 2, sqrt 3, sqrt 5, ...)'.  The square classes of '-1'
  and of the primes are 'F_2'-linearly independent in 'Q^×/(Q^×)^2', so
  'Gal(E/Q) ≅ ∏_l Z/2' with the product topology ('l' ranges over the
  primes and the infinite place).
* The direct sum 'D = ⊕_l Z/2' is dense in '∏_l Z/2'.
* '(∏_l Z/2)/D' is an infinite-dimensional 'F_2'-vector space, so it has a
  subspace of codimension 'n' (e.g. 'n = 2').  Its preimage 'Q_n' has index
  '2 ^ n', contains 'D', and is dense.  A dense open subgroup is closed and
  dense, hence equal to the whole group, contradiction; so 'Q_n' is not open.
* Pull back along the continuous surjective restriction map
  'Gal(Qbar/Q) ↠ Gal(E/Q)' (which is a quotient map of profinite groups);
  the preimage is a non-open finite-index subgroup of 'Gal(Qbar/Q)'.

The same construction works over any number field 'K': choose rational primes
'q_1, q_2, ...' unramified in 'K'.  Their classes in 'K^×/(K^×)^2' are
'F_2'-independent (use the valuation at a prime ideal above 'q_i'), so the
compositum 'L = K(sqrt q_1, sqrt q_2, ...)' is Galois over 'K' with
'Gal(L/K) ≅ ∏_i Z/2'.  Repeat the dense-direct-sum argument in this product
and pull back along 'G_K ↠ Gal(L/K)'.  This applies to 'K = S1720Field'.

Milne's proof uses Zorn's lemma; his Aside 7.31 notes that it is consistent
with ZF+DC that every homomorphism from a second-countable profinite group
to a finite group is continuous.  So the failure is nonconstructive.

### What Mathlib has and what it does not have

Mathlib has the Krull topology and the infinite Galois correspondence
('Mathlib.FieldTheory.Galois.Profinite'), the compact-group lemmas
'Subgroup.isOpen_of_isClosed_of_finiteIndex' (a closed finite-index subgroup
is open) and 'Subgroup.isClosed_of_isOpen' (an open subgroup is closed), and
'Subgroup.index_comap_of_surjective'.

Mathlib does **not** have:

* any form of strong completeness: Nikolov--Segal ('every finitely generated
  profinite group is strongly complete') is absent; a search for
  'strongly complete' over Mathlib returns nothing;
* the Kummer-theoretic surjection 'G_K ↠ ∏ Z/2' for a number field 'K'
  (infinite composita of quadratic extensions; 'Mathlib.FieldTheory.KummerExtension'
  treats finite cyclic Kummer extensions only);
* the choice/ultrafilter construction of a non-open index-two subgroup of an
  infinite product '∏ Z/2' (equivalently, a discontinuous linear functional).

Adding any of these would not repair the target, because the target is false.
In particular, the absent Nikolov--Segal theorem only covers the finitely
generated case (finite fields, p-adic local fields), not number fields.

## Formal content of this file (no sorry, no new axioms)

1. 'S1751Target' and 'S1751S1720Target': the exact S1737 proposition at 'F'
   and at 'S1720Field'; 'S1751Refutation' and 'S1751S1720Refutation' are the
   negations.
2. 'S1751Target_iff_allFiniteActionsContinuous': S1737's equivalence, restated
   at the absolute Galois group.
3. 'S1751EveryFiniteIndexOpen_iff_closed': for a topological group the S1737
   condition is equivalent to 'every finite-index subgroup is closed', the
   form in which the literature states the counterexample.
3b. 'S1751topologicalClosure_finiteIndex_isOpen': the best true positive
   result: the closure of every finite-index subgroup of a topological group
   is open, so a failure can only come from a finite-index subgroup that is
   not closed.
4. 'S1751AbsoluteGalois_iff_closed': the specialization to 'G_F'.
5. 'S1751notEveryFiniteIndexOpen_of_quotient': strong completeness is
   inherited by quotient maps.  A continuous quotient map with a non-open
   finite-index subgroup of the target yields one in the source.  This is the
   exact group-theoretic transfer used by the counterexample.
6. 'S1751TargetFalse_of_quotient': the same statement at 'G_F'.
7. 'S1751NotAllFiniteActionsContinuous_of_nonOpen' and
   'S1751NotFundamentalGroup_of_nonOpen': a non-open finite-index subgroup
   refutes S1737's continuity condition and the literal full-action
   'IsFundamentalGroup' statement.
8. 'S1751S1720LiteralStatementFalse_of_nonOpen': the same at 'F = S1720Field'.
9. 'S1751NonOpenSubgroupMissing': the precise external input, recorded as a
   proposition.  It is TRUE for number fields by Milne's Proposition 7.29 and
   the adaptation above, but it is not proved in Mathlib and is not asserted
   here.  'S1751Refutation_of_missing' shows that this input is exactly what
   is needed to refute the target; no axiom or sorry is introduced.
-/

import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Maps.Basic
import tmp.sheaf.xif.paper.S1737FundamentalGroupFromGaloisActual
import tmp.sheaf.xif.paper.S1720SourceArithmeticActual

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

open CategoryTheory
open LeanFormal.IUT.XiFPaper.S1737FundamentalGroupFromGaloisActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open Topology
open scoped FintypeCatDiscrete

namespace LeanFormal.IUT.XiFPaper.S1751FiniteIndexOpenActual

/-! ## 1. The exact target and its negation -/

/-- The S1737 condition at 'G = Iut.AbsoluteGaloisProfinite F': every
finite-index subgroup of the absolute Galois group is open. -/
abbrev S1751Target (F : Type) [Field F] : Prop :=
  S1737AbsoluteGaloisEveryFiniteIndexSubgroupOpen F

/-- The same condition at the actual IUT field 'F = S1720Field'. -/
abbrev S1751S1720Target : Prop :=
  S1737AbsoluteGaloisEveryFiniteIndexSubgroupOpen S1720Field

/-- The negation of the S1737 condition at 'F'. -/
abbrev S1751Refutation (F : Type) [Field F] : Prop :=
  ¬ S1751Target F

/-- The negation at the actual IUT field. -/
abbrev S1751S1720Refutation : Prop :=
  ¬ S1751S1720Target

/-- The precise external input of the counterexample at a field 'F': a
finite-index subgroup of 'G_F' which is not open.  For a number field this is
supplied by Milne's Proposition 7.29 and its adaptation (see the module
docstring).  This definition is only a proposition; it is NOT asserted here
and no axiom is introduced. -/
def S1751NonOpenSubgroupMissing (F : Type) [Field F] : Prop :=
  ∃ H : Subgroup (Iut.AbsoluteGaloisProfinite F),
    H.FiniteIndex ∧ ¬ IsOpen (H : Set (Iut.AbsoluteGaloisProfinite F))

/-- The external input at 'F = S1720Field'. -/
abbrev S1751S1720NonOpenSubgroupMissing : Prop :=
  S1751NonOpenSubgroupMissing S1720Field

/-- The external input implies the refutation.  This separates the group
theory (proved) from the number theory (Milne's construction, not
formalized). -/
theorem S1751Refutation_of_missing (F : Type) [Field F]
    (h : S1751NonOpenSubgroupMissing F) : S1751Refutation F := by
  intro htarget
  obtain ⟨H, hHfin, hHopen⟩ := h
  exact hHopen (htarget H hHfin)

theorem S1751S1720Refutation_of_missing
    (h : S1751S1720NonOpenSubgroupMissing) : S1751S1720Refutation :=
  S1751Refutation_of_missing S1720Field h

/-! ## 2. Relation with S1737's continuity condition -/

theorem S1751Target_iff_allFiniteActionsContinuous (F : Type) [Field F] :
    S1751Target F ↔ S1737AbsoluteGaloisActionForgetMissing F :=
  (S1737AbsoluteGaloisActionForgetMissing_iff_everyFiniteIndexOpen F).symm

/-- A non-open finite-index subgroup refutes 'every finite action is
continuous', the missing hypothesis isolated in S1737. -/
theorem S1751NotAllFiniteActionsContinuous_of_nonOpen
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) [H.FiniteIndex] (hH : ¬ IsOpen (H : Set G)) :
    ¬ S1737AllFiniteActionsContinuous G := by
  intro h
  exact hH (S1737EveryFiniteIndexSubgroupOpen_of_allContinuous G h H ‹H.FiniteIndex›)

/-! ## 3. Finite-index open versus finite-index closed -/

/-- In a topological group, 'every finite-index subgroup is open' is
equivalent to 'every finite-index subgroup is closed'.  This is the form in
which the number-field counterexample is usually stated: Milne's subgroups
are non-open, hence (being finite-index) also non-closed. -/
theorem S1751EveryFiniteIndexOpen_iff_closed
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    S1737EveryFiniteIndexSubgroupOpen G ↔
      ∀ H : Subgroup G, H.FiniteIndex → IsClosed (H : Set G) := by
  constructor
  · intro h H hH
    exact Subgroup.isClosed_of_isOpen H (h H hH)
  · intro h H hH
    exact Subgroup.isOpen_of_isClosed_of_finiteIndex H (h H hH)

/-- The S1737 condition at an absolute Galois group, in closed form. -/
theorem S1751AbsoluteGalois_iff_closed (F : Type) [Field F] :
    S1751Target F ↔
      ∀ H : Subgroup (Iut.AbsoluteGaloisProfinite F),
        H.FiniteIndex → IsClosed (H : Set (Iut.AbsoluteGaloisProfinite F)) := by
  simpa [S1751Target, S1737AbsoluteGaloisEveryFiniteIndexSubgroupOpen,
    S1737AbsoluteGalois, S1737EveryFiniteIndexSubgroupOpen] using
    S1751EveryFiniteIndexOpen_iff_closed (Iut.AbsoluteGaloisProfinite F)

/-! ## 3b. The best true positive result: finite-index closures are open -/

/-- In a topological group, the closure of every finite-index subgroup is
open.  Hence a finite-index subgroup can fail to be open only by failing to
be closed, which is exactly what Milne's counterexample produces. -/
theorem S1751topologicalClosure_finiteIndex_isOpen
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) [H.FiniteIndex] :
    IsOpen (H.topologicalClosure : Set G) := by
  haveI : H.topologicalClosure.FiniteIndex :=
    Subgroup.finiteIndex_of_le (Subgroup.le_topologicalClosure H)
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex H.topologicalClosure
    H.isClosed_topologicalClosure

/-- The closure statement at an absolute Galois group. -/
theorem S1751AbsoluteGalois_topologicalClosure_isOpen (F : Type) [Field F]
    (H : Subgroup (Iut.AbsoluteGaloisProfinite F)) [H.FiniteIndex] :
    IsOpen (H.topologicalClosure : Set (Iut.AbsoluteGaloisProfinite F)) :=
  S1751topologicalClosure_finiteIndex_isOpen _ H

/-! ## 4. Transfer of non-strong-completeness along quotient maps -/

/-- Strong completeness is inherited by quotient maps: if a continuous
quotient map 'π : G →* Q' has a finite-index subgroup 'H ≤ Q' that is not
open, then 'G' has a finite-index subgroup (the preimage of 'H') that is not
open.  This is the exact group-theoretic transfer used in the number-field
counterexample, where 'Q = ∏ Z/2' and 'G = G_K'. -/
theorem S1751notEveryFiniteIndexOpen_of_quotient
    {G Q : Type*} [Group G] [TopologicalSpace G] [Group Q] [TopologicalSpace Q]
    (π : G →* Q) (hπ : IsQuotientMap π)
    (H : Subgroup Q) [H.FiniteIndex] (hH : ¬ IsOpen (H : Set Q)) :
    ∃ K : Subgroup G, K.FiniteIndex ∧ ¬ IsOpen (K : Set G) := by
  refine ⟨H.comap π, ?_, ?_⟩
  · rw [Subgroup.finiteIndex_iff]
    rw [Subgroup.index_comap_of_surjective (f := π) H hπ.surjective]
    exact Subgroup.FiniteIndex.index_ne_zero
  · intro hK
    apply hH
    rw [Subgroup.coe_comap H π] at hK
    exact hπ.isOpen_preimage.mp hK

/-- The quotient transfer at 'G = G_F'.  This is the precise logical shape of
the number-field refutation: it remains to produce a continuous quotient of
'G_F' with a finite-index non-open subgroup. -/
theorem S1751TargetFalse_of_quotient
    (F : Type) [Field F]
    {Q : Type} [Group Q] [TopologicalSpace Q]
    (π : Iut.AbsoluteGaloisProfinite F →* Q) (hπ : IsQuotientMap π)
    (H : Subgroup Q) [H.FiniteIndex] (hH : ¬ IsOpen (H : Set Q)) :
    S1751Refutation F := by
  intro h
  obtain ⟨K, hKfin, hKopen⟩ := S1751notEveryFiniteIndexOpen_of_quotient π hπ H hH
  exact hKopen (h K hKfin)

/-! ## 5. Consequence for the literal full-action fundamental-group statement -/

/-- A non-open finite-index subgroup refutes the literal full-action
'IsFundamentalGroup' statement at 'G'. -/
theorem S1751NotFundamentalGroup_of_nonOpen
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G]
    (H : Subgroup G) [H.FiniteIndex] (hH : ¬ IsOpen (H : Set G)) :
    ¬ PreGaloisCategory.IsFundamentalGroup (Action.forget FintypeCat.{0} G) G := by
  intro hfund
  exact S1751NotAllFiniteActionsContinuous_of_nonOpen G H hH
    (S1737AllFiniteActionsContinuous_of_isFundamentalGroup G hfund)

/-- The literal full-action statement at the actual IUT field fails as soon as
a non-open finite-index subgroup of 'G_{S1720Field}' is supplied.  Milne's
Proposition 7.29 (adapted to number fields, see the module docstring)
supplies such a subgroup. -/
theorem S1751S1720LiteralStatementFalse_of_nonOpen
    (H : Subgroup (Iut.AbsoluteGaloisProfinite S1720Field))
    [H.FiniteIndex]
    (hH : ¬ IsOpen (H : Set (Iut.AbsoluteGaloisProfinite S1720Field))) :
    ¬ PreGaloisCategory.IsFundamentalGroup
        (Action.forget FintypeCat.{0} (Iut.AbsoluteGaloisProfinite S1720Field))
        (Iut.AbsoluteGaloisProfinite S1720Field) :=
  S1751NotFundamentalGroup_of_nonOpen _ H hH

/-! ## 6. Axiom check and statement check -/

#print axioms S1751topologicalClosure_finiteIndex_isOpen
#print axioms S1751EveryFiniteIndexOpen_iff_closed
#print axioms S1751notEveryFiniteIndexOpen_of_quotient
#print axioms S1751TargetFalse_of_quotient
#print axioms S1751NotFundamentalGroup_of_nonOpen

#check S1751Target
#check S1751S1720Target
#check S1751Refutation
#check S1751S1720Refutation
#check S1751NonOpenSubgroupMissing
#check S1751S1720NonOpenSubgroupMissing
#check S1751Refutation_of_missing
#check S1751S1720Refutation_of_missing
#check S1751Target_iff_allFiniteActionsContinuous
#check S1751AbsoluteGalois_iff_closed
#check S1751topologicalClosure_finiteIndex_isOpen
#check S1751AbsoluteGalois_topologicalClosure_isOpen
#check S1751NotAllFiniteActionsContinuous_of_nonOpen
#check S1751S1720LiteralStatementFalse_of_nonOpen

end LeanFormal.IUT.XiFPaper.S1751FiniteIndexOpenActual
