import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import tmp.sheaf.xif.paper.Mzk1Lemma24StatementShapeActual
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: P1Morphism|PreservesSet|AvoidsPoint|UnramifiedOver|s3135_Lemma24StatementShape_proved|normalization -> hits Mzk1P1MorphismInterfaceActual:31-102 (P1Point/P1Morphism/PreservesSet/AvoidsPoint/UnramifiedOver/Mzk1Lemma24StatementShape) + Mzk1Lemma24StatementShapeActual:23 (s3135_Lemma24StatementShape_proved; conditional on |alpha|<=1 and beta large) + Mzk1Lemma23NormalizationActual (abc numeric normalization existence over ℂ; no transfer) -> REUSE/ADAPT (pointwise transport layer requested by abc: P1Morphism.comp + comp_preservesSet/avoidsPoint/unramifiedOver + mzk1_normalization_transfer; plus affine x |-> c(x-a) conjugation + statement-shape transfer).

# Mzk1Lemma24NormalizationTransferActual — Lemma 2.4/2.3 normalization transfer on the stage4 P1 interface

Corpus: papers/motizuki_corpus/text/Noncritical Belyi Maps.txt, Lemma 2.3 (normalization)
and Lemma 2.4 (144-160/183-206).  The two normalization hypotheses of
s3135_Lemma24StatementShape_proved are exactly (i) |alpha| <= 1 on S and (ii) the
beta-large threshold b + C*d <= |beta| (b from (M1b) beta-avoidance).  This file
provides the TRANSFER layer:
* P1Morphism.comp with a pointwise point map, and transport of the three predicates
  (pointwise; no injectivity needed);
* the affine normalizing map x |-> c*(x-a) on P^1 with its inverse and conjugation
  action, plus statement-shape transfer back to the original data;
* mzk1_normalization_transfer (abc's requested signature) and its bundle version.
The numerical normalization existence (choice of t, lam) stays with abc's
Mzk1Lemma23NormalizationActual; this file only transports along a given map.
No fake data; registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual.P1Morphism

/-- Precompose a P1Morphism's point map with a pointwise map (no injectivity needed). -/
def comp {K : Type u} [Field K] (φ : P1Morphism K) (h : P1Point K → P1Point K) :
    P1Morphism K where
  ratFunc := φ.ratFunc
  mapPoints := fun z => φ.mapPoints (h z)
  nonconstant := φ.nonconstant
  nonconstant_proof := φ.nonconstant_proof

end LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual.P1Morphism

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24NormalizationTransferActual

universe u

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24StatementShapeActual

variable {K : Type u} [Field K]

local instance : DecidableEq (P1Point ℂ) := Classical.decEq _

/-! ## Pointwise composition and predicate transport (abc signature) -/



/-- Transport of PreservesSet along a pointwise precomposition. -/
theorem comp_preservesSet (φ : P1Morphism K) (h : P1Point K → P1Point K)
    {S T : Set (P1Point K)} (hφ : PreservesSet φ (h '' S) T) :
    PreservesSet (φ.comp h) S T := by
  intro p hp
  exact hφ _ ⟨p, hp, rfl⟩

/-- Transport of AvoidsPoint along a pointwise precomposition. -/
theorem comp_avoidsPoint (φ : P1Morphism K) (h : P1Point K → P1Point K)
    {β : P1Point K} {T : Set (P1Point K)} (hφ : AvoidsPoint φ (h β) T) :
    AvoidsPoint (φ.comp h) β T :=
  hφ

/-- Transport of UnramifiedOver along a pointwise precomposition. -/
theorem comp_unramifiedOver (φ : P1Morphism K) (h : P1Point K → P1Point K)
    {T : Set (P1Point K)} {unramifiedAt : P1Point K → Prop}
    (hφ : UnramifiedOver φ T unramifiedAt) :
    UnramifiedOver (φ.comp h) T (fun z => unramifiedAt (h z)) := by
  intro z hz
  exact hφ (h z) hz

/-- **abc's requested transfer signature (pointwise normalization transfer).** -/
theorem mzk1_normalization_transfer (S : Finset ℂ) (β : ℂ)
    (h : P1Point ℂ → P1Point ℂ) (targetSet : Set (P1Point ℂ))
    (unramifiedAt : P1Point ℂ → Prop)
    (hshape : ∃ φ : P1Morphism ℂ, φ.nonconstant ∧
      PreservesSet φ (↑(S.image (fun a => h (P1Point.ofFinite a))) : Set (P1Point ℂ)) targetSet ∧
      AvoidsPoint φ (h (P1Point.ofFinite β)) targetSet ∧
      UnramifiedOver φ {p | p ∉ targetSet} unramifiedAt) :
    ∃ φ' : P1Morphism ℂ, φ'.nonconstant ∧
      PreservesSet φ' (↑(S.image P1Point.ofFinite) : Set (P1Point ℂ)) targetSet ∧
      AvoidsPoint φ' (P1Point.ofFinite β) targetSet ∧
      UnramifiedOver φ' {p | p ∉ targetSet} (fun p => unramifiedAt (h p)) :=
  by
    rcases hshape with ⟨φ, hnc, hpres, hav, hunr⟩
    refine ⟨φ.comp h, hnc, ?_, ?_, ?_⟩
    · intro p hp
      rcases Finset.mem_image.mp hp with ⟨a, haS, rfl⟩
      exact hpres _ (Finset.mem_image_of_mem (fun a => h (P1Point.ofFinite a)) haS)
    · exact comp_avoidsPoint φ h hav
    · exact comp_unramifiedOver φ h hunr

/-- Bundle version: transfer a full Lemma-2.4 statement shape along a pointwise map. -/
theorem mzk1_normalization_transfer_shape (S : Finset ℂ) (β : ℂ)
    (h : P1Point ℂ → P1Point ℂ) (targetSet : Set (P1Point ℂ))
    (unramifiedAt : P1Point ℂ → Prop)
    (hshape : Mzk1Lemma24StatementShape ℂ
      (S.image (fun a => h (P1Point.ofFinite a))) (h (P1Point.ofFinite β))
      targetSet unramifiedAt) :
    Mzk1Lemma24StatementShape ℂ (S.image P1Point.ofFinite) (P1Point.ofFinite β)
      targetSet (fun p => unramifiedAt (h p)) :=
  by
    rcases hshape with ⟨φ, hnc, hpres, hav, hunr⟩
    refine ⟨φ.comp h, hnc, ?_, ?_, ?_⟩
    · intro p hp
      rcases Finset.mem_image.mp hp with ⟨a, haS, rfl⟩
      exact hpres _ (Finset.mem_image_of_mem (fun a => h (P1Point.ofFinite a)) haS)
    · exact comp_avoidsPoint φ h hav
    · exact comp_unramifiedOver φ h hunr

/-! ## Affine normalizing map x |-> c*(x-a) on P^1 and conjugation -/

/-- The affine normalizing map x |-> c * (x - a) of the affine line (c != 0). -/
structure P1Affine (K : Type u) [Field K] where
  a : K
  c : K
  c_ne_zero : c ≠ 0

namespace P1Affine

variable (g : P1Affine K)

/-- The affine formula c * (x - a). -/
def fin (x : K) : K := g.c * (x - g.a)

/-- Inverse affine formula y / c + a. -/
def invFin (y : K) : K := y / g.c + g.a

/-- The action on P^1 (infinity fixed). -/
def toMap : P1Point K → P1Point K := fun z => z.map g.fin

/-- The inverse action on P^1. -/
def invMap : P1Point K → P1Point K := fun z => z.map g.invFin

/-- The inverse action inverts the affine action. -/
theorem invMap_toMap (z : P1Point K) : g.invMap (g.toMap z) = z := by
  cases z with
  | none => rfl
  | some x =>
      simp only [toMap, invMap, fin, invFin, Option.map_some]
      congr 1
      field_simp [g.c_ne_zero]
      ring

/-- The affine action inverts the inverse action. -/
theorem toMap_invMap (z : P1Point K) : g.toMap (g.invMap z) = z := by
  cases z with
  | none => rfl
  | some y =>
      simp only [toMap, invMap, fin, invFin, Option.map_some]
      congr 1
      field_simp [g.c_ne_zero]
      ring

/-- The affine action is injective. -/
theorem toMap_injective : Function.Injective g.toMap := by
  intro x y hxy
  have h := congrArg g.invMap hxy
  simpa [invMap_toMap] using h

end P1Affine

/-- Conjugated morphism under the affine normalizing map. -/
def conj (φ : P1Morphism K) (g : P1Affine K) : P1Morphism K where
  ratFunc := φ.ratFunc
  mapPoints := fun z => g.invMap (φ.mapPoints (g.toMap z))
  nonconstant := φ.nonconstant
  nonconstant_proof := φ.nonconstant_proof

/-- Transport of PreservesSet through the conjugated morphism. -/
theorem conj_preservesSet (φ : P1Morphism K) (g : P1Affine K)
    {S T : Set (P1Point K)}
    (hφ : PreservesSet φ (g.toMap '' S) (g.toMap '' T)) :
    PreservesSet (conj φ g) S T := by
  intro p hp
  have hmap : g.toMap p ∈ g.toMap '' S := ⟨p, hp, rfl⟩
  have hmem := hφ _ hmap
  rcases hmem with ⟨t, ht, hteq⟩
  have hvalue : g.invMap (φ.mapPoints (g.toMap p)) = t := by
    rw [← hteq, P1Affine.invMap_toMap]
  simpa only [conj, hvalue] using ht

/-- Transport of AvoidsPoint through the conjugated morphism. -/
theorem conj_avoidsPoint (φ : P1Morphism K) (g : P1Affine K)
    {β : P1Point K} {T : Set (P1Point K)}
    (hφ : AvoidsPoint φ (g.toMap β) (g.toMap '' T)) :
    AvoidsPoint (conj φ g) β T := by
  intro hmem
  apply hφ
  refine ⟨g.invMap (φ.mapPoints (g.toMap β)), ?_, ?_⟩
  · simpa only [conj, P1Affine.toMap_invMap] using hmem
  · rw [P1Affine.toMap_invMap]

/-- Transport of UnramifiedOver through the conjugated morphism (predicate conjugated
by the affine map). -/
theorem conj_unramifiedOver (φ : P1Morphism K) (g : P1Affine K)
    {T : Set (P1Point K)} {unramifiedAt : P1Point K → Prop}
    (hφ : UnramifiedOver φ (g.toMap '' T) unramifiedAt) :
    UnramifiedOver (conj φ g) T (fun z => unramifiedAt (g.toMap z)) := by
  intro z hz
  apply hφ
  refine ⟨g.invMap (φ.mapPoints (g.toMap z)), ?_, ?_⟩
  · simpa only [conj, P1Affine.toMap_invMap] using hz
  · rw [P1Affine.toMap_invMap]

/-- **Statement-shape transfer:** a witness for the affine-normalized data
(S.image g.toMap, g.toMap β, g.toMap '' T) yields a witness for the original data
(S, β, T) with the unramified predicate conjugated by g. -/
theorem transfer_statementShape {K : Type u} [Field K] [DecidableEq K]
    (g : P1Affine K)
    {S : Finset (P1Point K)} {T : Set (P1Point K)} {β : P1Point K}
    {unramifiedAt : P1Point K → Prop}
    (h : Mzk1Lemma24StatementShape K (S.image (fun p => g.toMap p)) (g.toMap β)
      (g.toMap '' T) unramifiedAt) :
    Mzk1Lemma24StatementShape K S β T (fun p => unramifiedAt (g.toMap p)) := by
  rcases h with ⟨φ, hnc, hpres, hav, hunr⟩
  refine ⟨conj φ g, hnc, ?_, ?_, ?_⟩
  · intro p hp
    have hpin : g.toMap p ∈ S.image (fun p => g.toMap p) :=
      Finset.mem_image_of_mem _ hp
    have hmem := hpres _ hpin
    rcases hmem with ⟨t, ht, hteq⟩
    have hvalue : g.invMap (φ.mapPoints (g.toMap p)) = t := by
      rw [← hteq, P1Affine.invMap_toMap]
    simpa only [conj, hvalue] using ht
  · intro hmem
    apply hav
    have hmapT : g.invMap (φ.mapPoints (g.toMap β)) ∈ T := by
      simpa only [conj] using hmem
    refine ⟨g.invMap (φ.mapPoints (g.toMap β)), hmapT, ?_⟩
    rw [P1Affine.toMap_invMap]
  · intro z hz
    apply hunr
    intro hmem
    rcases hmem with ⟨t, ht, hteq⟩
    apply hz
    have hval : (conj φ g).mapPoints z = t := by
      simp only [conj]
      rw [← hteq, P1Affine.invMap_toMap]
    simpa only [hval] using ht

/-- Transfer rows (class A proved vs named residuals). -/
def normalizationTransferRows : List (String × String × String) :=
  [ ("pointwise composition P1Morphism.comp + predicate transport", "A", "PROVED comp_preservesSet / comp_avoidsPoint / comp_unramifiedOver")
  , ("abc transfer signature mzk1_normalization_transfer", "A", "PROVED (pointwise; no injectivity needed)")
  , ("bundle transfer mzk1_normalization_transfer_shape", "A", "PROVED (full Mzk1Lemma24StatementShape transfer)")
  , ("affine map x |-> c*(x-a) on P^1 with inverse and conjugation", "A", "DEFINED P1Affine/toMap/invMap/conj + inverse laws")
  , ("statement-shape transfer along an affine normalizing map", "A", "PROVED transfer_statementShape")
  , ("numeric normalization existence (choice of t, lam)", "B", "abc's Mzk1Lemma23NormalizationActual (in progress); not re-built here")
  , ("application to s3135 two hypotheses (|alpha|<=1, beta large)", "A/B", "transfer layer ready; numeric normalization + s3135 wiring is the next consumer step (abc nested assembly)") ]

/-- The transfer row record has seven rows. -/
theorem normalizationTransferRows_length : normalizationTransferRows.length = 7 := rfl

#check P1Morphism.comp
#check mzk1_normalization_transfer
#check mzk1_normalization_transfer_shape
#check P1Affine
#check transfer_statementShape
#check normalizationTransferRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Lemma24NormalizationTransferActual
end