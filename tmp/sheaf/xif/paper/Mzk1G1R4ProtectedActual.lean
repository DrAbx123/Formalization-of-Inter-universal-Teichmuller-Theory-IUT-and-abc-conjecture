/-
Mzk1G1R4ProtectedActual — R4: general protected points producer (route §6.2–6.3).

MODEL.  `Place K F` / `Divisor K F` are the flt_core function-field model of the places and
divisors of a smooth proper curve (`Def_AlgebraicCurve_DivisorClassGroup`, ported and imported
transitively here).  `Y_n` enters only through its function field: the wiring "the function field
of `fermatCurveScheme n` over an algebraically closed `k` carries the Riemann–Roch instance bundle" is
recorded as `RRAvailable` below, and is the ONE honest residual
(obligation: FERMAT-FUNCTION-FIELD-BUNDLE); it has NO inhabitant in this file.

DELIVERED (all proved, no sorry/axiom):
* actual finite point sets `S T : Finset (Place K F)`;
* actual reduced effective divisor `D = pointDivisor T = Σ_{t∈T} [t]` with `supp D = T`;
* `T ⊆ supp D`, `supp D ∩ S = ∅` (from `S ∩ T = ∅`);
* actual sections: `s0 = 1 ∈ L(D)`, whose section-divisor is `D` (`sectionOrder D s0 = D`),
  and `s1 = g⁻¹` where `g` comes from the PROVED Riemann–Roch producer
  `zero_divisor_exists_proved` (zeros exactly `T`, all simple); `s1` is nonzero on `D`
  (`sectionOrder D s1 = 0` on `supp D`);
* `psi = s0 / s1 = g` with `psi⁻¹(0) = supp D`, `0 ∉ psi(S)`, `0 ∉ Branch psi`
  (explicit ord characterization: every zero of `psi` is simple);
* Galois stability: `GaloisStable T` is the explicit orbit-union characterization using
  the `F ≃ₐ[K] F`-action on `Place K F`; it implies `σ • D = D`;
* §6.3 ratio-inversion glue data on `D(s1)` / `D(s0)`;
* **H¹-vanishing bundle** `H1VanishingData` (paper H¹ inputs as PORTED FLT interface props:
  `ConstantsAreBase`, `ResidueTheorem`, `WeilDualityAdelic`, `h1_vanish`) together with
  `indexFormula`, the Riemann-equality form `ell D = deg D + 1 - g`, and the donor bridge to
  `WeilDuality`; no `sorry`;
* size existence form: `∃ T', T ⊆ T' ∧ 2g+1 ≤ T'.card ∧ Disjoint T' S`
  (`exists_superset_card_disjoint`, `protectedPointData_size_exists`), and its degree form
  `deg (pointDivisor T') = #T'` (`degree_pointDivisor`, `exists_superset_card_disjoint_deg`,
  `protectedPointData_size_exists_deg`);
* **H¹ route to `s1`**: `H1VanishingData` + `RiemannIndexFormula` give the strict drop
  `L(D - [t]) < L(D)` (`H1VanishingData.lSpace_sub_single_lt`, where `h1_vanish` is consumed);
  the A3/B2 evaluation lemma `exists_forall_apply_ne_zero` applied to the evaluation maps
  (`A3EvalMaps`, obligation A3-EVAL-MAPS) yields the `s1` selector
  `exists_s1_nonzero_on_of_h1` and the producer `protectedPointData_exists_of_h1`
  (`s0 = 1`, `psi = s0/s1 = s1⁻¹`, simple zeros exactly `supp D`);
* `§6.2 (iv)` in consolidated form: `psi⁻¹(0) = supp D`, `0 ∉ psi(S)`, `0 ∉ Branch psi`
  (`ProtectedPointData.psi_structure`).

ROOT NOTE.  The donor paths in `coord/R4-H1-VANISHING-DATA-DOC.md` name the `flt` root
(`tmp.external.ported.flt.Definitions.*`); this file lives on the `flt_core` root, and the two
roots duplicate the whole `AlgebraicCurve` API, so they cannot be imported into one file.  The
`flt_core` mirrors of the same four files are imported instead: identical declaration names and
identical line refs (`ConstantsAreBase`:48, `indexOfSpecialty`:139, `RiemannIndexFormula`:23,
`WeilDualityAdelic`:28, `weilDuality_of_riemannIndex_of_adelic`:59, `ResidueTheorem`:110).

OBLIGATIONS left open here are tagged `(obligation: ...)`:
* **FERMAT-FUNCTION-FIELD-BUNDLE** (`RRAvailable`, no inhabitant): the wiring of the function
  field of `Y_n` to the Riemann–Roch instance bundle;
* **A3-EVAL-MAPS** (`A3EvalMaps D`, no inhabitant): the evaluation maps of `O(D)`-sections at
  the places, with kernel "vanishes at `p`" --- the Serre-duality corollary
  `H¹(O(D - [p])) = 0 ⇒ ev_p` surjective.  The H¹ producer `protectedPointData_exists_of_h1`
  consumes it; the unconditional producer `protectedPointData_exists` does not (its `s1` comes
  from the PROVED Riemann–Roch pencil `zero_divisor_exists_proved`).
-/
import tmp.sheaf.xif.paper.Mzk1GeomCoreRRProvedActual
import tmp.sheaf.xif.paper.Mzk1G1A3EvaluationActual
import tmp.external.ported.flt_core.Definitions.Def_AlgebraicCurve_AdelicIndex
import tmp.external.ported.flt_core.Definitions.Def_AlgebraicCurve_RiemannRochRows
import tmp.external.ported.flt_core.Definitions.Def_AlgebraicCurve_WeilOfKaehler

noncomputable section
set_option maxHeartbeats 1000000
set_option autoImplicit false

open AlgebraicCurve
open KaehlerDifferential

namespace LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual

open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreRRProvedActual

/-! ## Part 1. The divisor layer (no Riemann–Roch needed) -/

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Support of a divisor, as a set of places (no decidable equality on `Place K F` needed). -/
def suppSet (D : Divisor K F) : Set (Place K F) := {p | D p ≠ 0}

theorem mem_suppSet {D : Divisor K F} {p : Place K F} : p ∈ suppSet D ↔ D p ≠ 0 := Iff.rfl

/-- Order of the section `f ∈ L(D)` of `O(D)` at `p`: `ord_p f + D p`.  Zero means the
section does not vanish at `p`; `p ↦ sectionOrder D f p` is the divisor of the section. -/
def sectionOrder (D : Divisor K F) (f : F) (p : Place K F) : ℤ := p.ord f + D p

/-- The reduced effective divisor of a finite point set: `D = Σ_{t ∈ T} [t]`. -/
def pointDivisor (T : Finset (Place K F)) : Divisor K F := punctureDivisor T

theorem pointDivisor_apply_of_mem {T : Finset (Place K F)} {v : Place K F} (hv : v ∈ T) :
    pointDivisor T v = 1 := punctureDivisor_apply_of_mem hv

theorem pointDivisor_apply_of_notMem {T : Finset (Place K F)} {v : Place K F} (hv : v ∉ T) :
    pointDivisor T v = 0 := punctureDivisor_apply_of_notMem hv

theorem pointDivisor_apply_ne_zero_iff {T : Finset (Place K F)} {p : Place K F} :
    pointDivisor T p ≠ 0 ↔ p ∈ T := by
  constructor
  · intro h
    by_contra hc
    exact h (pointDivisor_apply_of_notMem hc)
  · intro h
    rw [pointDivisor_apply_of_mem h]
    exact one_ne_zero

/-- The support of `pointDivisor T` is exactly `T`. -/
theorem pointDivisor_support (T : Finset (Place K F)) :
    suppSet (pointDivisor T) = (↑T : Set (Place K F)) := by
  ext p
  rw [mem_suppSet, pointDivisor_apply_ne_zero_iff]
  simp

theorem pointDivisor_effective (T : Finset (Place K F)) :
    ∀ p : Place K F, 0 ≤ pointDivisor T p := by
  intro p
  by_cases h : p ∈ T
  · rw [pointDivisor_apply_of_mem h]; norm_num
  · rw [pointDivisor_apply_of_notMem h]

theorem pointDivisor_reduced (T : Finset (Place K F)) :
    ∀ p : Place K F, pointDivisor T p ≤ 1 := by
  intro p
  by_cases h : p ∈ T
  · rw [pointDivisor_apply_of_mem h]
  · rw [pointDivisor_apply_of_notMem h]; norm_num

theorem pointDivisor_subset_supp (T : Finset (Place K F)) :
    (↑T : Set (Place K F)) ⊆ suppSet (pointDivisor T) := by
  intro p hp
  have hpT : p ∈ T := by simpa using hp
  rw [mem_suppSet, pointDivisor_apply_of_mem hpT]
  exact one_ne_zero

theorem pointDivisor_supp_subset (T : Finset (Place K F)) :
    suppSet (pointDivisor T) ⊆ (↑T : Set (Place K F)) := by
  intro p hp
  have hpne : pointDivisor T p ≠ 0 := hp
  simpa using pointDivisor_apply_ne_zero_iff.mp hpne

/-- `supp D` and `S` are disjoint as soon as `S` avoids `T` (for `D = pointDivisor T`). -/
theorem pointDivisor_disjoint_of_notMem {S T : Finset (Place K F)}
    (hS : ∀ s ∈ S, s ∉ T) :
    Disjoint (suppSet (pointDivisor T)) (↑S : Set (Place K F)) := by
  rw [pointDivisor_support T]
  exact Set.disjoint_left.mpr (by
    intro a ha hb
    exact hS a hb (by simpa using ha))

/-- **Size existence form.**  A finite point set `T` with `n ≤ #T` can always be enlarged to a
`T'` still meeting the bound and disjoint from `S` whenever `S` avoids `T`.  For the R4 input
`n = 2g+1` the set `T` itself already works: no enlargement is needed. -/
theorem exists_superset_card_disjoint (n : ℕ) (S T : Finset (Place K F))
    (hcard : n ≤ T.card) (hS : ∀ s ∈ S, s ∉ T) :
    ∃ T' : Finset (Place K F), T ⊆ T' ∧ n ≤ T'.card ∧ Disjoint T' S :=
  ⟨T, le_rfl, hcard, Finset.disjoint_left.mpr fun a haT haS => hS a haS haT⟩

/-- Explicit (orbit-union) characterization of Galois stability of a finite point set: it is
stable under the `K`-automorphism action on places.  This replaces a formalized Galois group
action on `Y_n`; it is the assumption used downstream. -/
def GaloisStable (T : Finset (Place K F)) : Prop :=
  ∀ (σ : F ≃ₐ[K] F) (p : Place K F), σ • p ∈ T ↔ p ∈ T

theorem mem_smul_iff_of_galoisStable {T : Finset (Place K F)} (hT : GaloisStable T)
    (σ : F ≃ₐ[K] F) (p : Place K F) : σ • p ∈ T ↔ p ∈ T := hT σ p

/-- Galois stability of `T` makes the divisor `D = Σ_{t ∈ T} [t]` Galois invariant. -/
theorem pointDivisor_galois_invariant {T : Finset (Place K F)}
    (hT : GaloisStable (K := K) (F := F) T) (σ : F ≃ₐ[K] F) :
    σ • pointDivisor T = pointDivisor T := by
  apply Finsupp.ext
  intro w
  rw [Divisor.smul_apply]
  by_cases h : w ∈ T
  · have h' : σ⁻¹ • w ∈ T := (hT σ⁻¹ w).mpr h
    rw [pointDivisor_apply_of_mem h', pointDivisor_apply_of_mem h]
  · have h' : σ⁻¹ • w ∉ T := by
      intro hc
      have hw : σ • (σ⁻¹ • w) ∈ T := (hT σ (σ⁻¹ • w)).mpr hc
      rw [smul_inv_smul] at hw
      exact h hw
    rw [pointDivisor_apply_of_notMem h', pointDivisor_apply_of_notMem h]

/-! ## Part 1b. The degree of the reduced point divisor, and the size form with degree -/

section SizeDegree

variable [IsAlgClosed K] [IsCurveOver K F]

/-- The degree of the reduced effective divisor `pointDivisor T = Σ_{t∈T} [t]` is `#T`
(donor: `degree_punctureDivisor`). -/
theorem degree_pointDivisor (T : Finset (Place K F)) :
    Divisor.degree (pointDivisor T) = (T.card : ℤ) :=
  degree_punctureDivisor T

/-- **Size existence form with degree.**  A finite point set `T` with `n ≤ #T` enlarges to `T'`
still above the bound and disjoint from `S`, and the reduced divisor `pointDivisor T'` has degree
exactly `#T'`.  For the R4 input `n = 2g+1` the set `T` itself works. -/
theorem exists_superset_card_disjoint_deg (n : ℕ) (S T : Finset (Place K F))
    (hcard : n ≤ T.card) (hS : ∀ s ∈ S, s ∉ T) :
    ∃ T' : Finset (Place K F), T ⊆ T' ∧ n ≤ T'.card ∧ Disjoint T' S ∧
      Divisor.degree (pointDivisor T') = (T'.card : ℤ) :=
  ⟨T, le_rfl, hcard, Finset.disjoint_left.mpr fun a haT haS => hS a haS haT,
    degree_pointDivisor T⟩

end SizeDegree

/-! ## Part 2. The RR instance bundle (obligation hook) -/

/-- The exact Riemann–Roch instance bundle consumed by the producer below.  Supplying it for the
function field of `Y_n = fermatCurveScheme n` is the remaining wiring
(obligation: FERMAT-FUNCTION-FIELD-BUNDLE).  There is NO inhabitant in this file. -/
structure RRAvailable (K F : Type*) [Field K] [Field F] [Algebra K F] : Type _ where
  isAlgClosed : IsAlgClosed K
  infinite : Infinite K
  decEqRatFunc : DecidableEq (RatFunc K)
  hasCanonicalDivisor : HasCanonicalDivisor (K := K) (F := F)
  dCoordGenerates_places : ∀ w : Place K F, w.DCoordGenerates
  algebraRatFunc : Algebra (RatFunc K) F
  isScalarTower : IsScalarTower K (RatFunc K) F
  isIntegral : Algebra.IsIntegral (RatFunc K) F
  moduleFinite : Module.Finite (RatFunc K) F
  hasLocalResidue : HasLocalResidue K F
  finiteResidue_places : ∀ w : Place K F, w.FiniteResidue
  nontrivialOmega : Nontrivial Ω[F⁄K]
  isCurveOver : IsCurveOver K F
  isCurveOverRatFunc : IsCurveOver K (RatFunc K)
  finiteResidue_ratFunc : ∀ u : Place K (RatFunc K), u.FiniteResidue
  hasCanonicalLocalResidueKStar : HasCanonicalLocalResidueKStar K F
  hasPrincipalDivisors : HasPrincipalDivisors K F
  isSeparable : Algebra.IsSeparable (RatFunc K) F
  nontrivialOmegaRatFunc : Nontrivial Ω[(RatFunc K)⁄K]
  dCoordGenerates_ratFunc : ∀ v : Place K (RatFunc K), v.DCoordGenerates
  finiteDimensional : FiniteDimensional (RatFunc K) F
  hasSeparableResidue : HasSeparableResidue K F

/-! ## Part 2b. The H¹-vanishing bundle (`H1VanishingData`, R4 paper interface) -/

/-- **R4 H¹-vanishing package.**  The paper's H¹-assembly inputs, all as PORTED FLT interface
propositions (`ConstantsAreBase`, `ResidueTheorem`, `WeilDualityAdelic`) plus the H¹-vanishing
statement `h1_vanish`.  `indexOfSpecialty`, `ell`, `Divisor.degree` and `genus` are the ported
`AlgebraicCurve` API (`flt_core` mirror of the `flt` donors cited in
`coord/R4-H1-VANISHING-DATA-DOC.md`; see the ROOT NOTE in the header).  No new assumption is
introduced: each field is one of the cited donors, and `h1_vanish` is the paper's `H¹ = 0`
input. -/
structure H1VanishingData (K F : Type*) [Field K] [Field F] [Algebra K F]
    [HasPrincipalDivisors K F] [HasCanonicalLocalResidueKStar K F]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] where
  /-- constants are exactly the base field (R4 pack: no extra constants). -/
  constantsAreBase : ConstantsAreBase K F
  /-- the residue theorem (sum of residues of an adelic form vanishes). -/
  residueTheorem : ResidueTheorem K F
  /-- Weil duality in adelic form (Prop-level). -/
  weilDualityAdelic : WeilDualityAdelic K F
  /-- the H¹-vanishing statement: the index of specialty vanishes identically. -/
  h1_vanish : ∀ D : Divisor K F, indexOfSpecialty D = 0

section H1

variable [HasPrincipalDivisors K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
variable [Nontrivial Ω[F⁄K]]

/-- The adelic duality field plus the index formula give `WeilDuality` (donor bridge
`weilDuality_of_riemannIndex_of_adelic`).  No extra instances are needed: `WeilDuality K F`
carries its own `[IsCurveOver]` `[HasCanonicalDivisor]` `[∀ v, v.DCoordGenerates]` binders. -/
theorem H1VanishingData.weilDuality (hD : H1VanishingData K F)
    (hRI : RiemannIndexFormula K F) : WeilDuality K F :=
  weilDuality_of_riemannIndex_of_adelic (K := K) (F := F) hRI hD.weilDualityAdelic

variable [IsCurveOver K F]

/-- The Riemann-index specialization: it IS the ported `RiemannIndexFormula` donor, so carrying
`h1_vanish` costs nothing here. -/
theorem H1VanishingData.indexFormula (hD : H1VanishingData K F)
    (hRI : RiemannIndexFormula K F) (D : Divisor K F) :
    (indexOfSpecialty D : ℤ) = (ell D : ℤ) - (Divisor.degree D + 1 - (genus K F : ℤ)) :=
  hRI D

/-- **H¹ = 0 turns the Riemann inequality into an equality**: `ell D = deg D + 1 - g`. -/
theorem H1VanishingData.ell_eq_degree_add_one (hD : H1VanishingData K F)
    (hRI : RiemannIndexFormula K F) (D : Divisor K F) :
    (ell D : ℤ) = Divisor.degree D + 1 - (genus K F : ℤ) := by
  have h := hRI D
  have h0 : (indexOfSpecialty D : ℤ) = 0 := by simp [hD.h1_vanish D]
  rw [h0] at h
  linarith

variable [IsAlgClosed K]

/-- **H¹ = 0 gives the strict drop of the section space at a single point.**  For the reduced
divisor `D = pointDivisor T`, subtracting `[t]` lowers `ell` by exactly one, so
`L(D - [t]) < L(D)` (the pencil at `t` is proper).  This is where `h1_vanish` is consumed:
via `ell_eq_degree_add_one` and `deg (pointDivisor T) = #T`. -/
theorem H1VanishingData.lSpace_sub_single_lt (hD : H1VanishingData K F)
    (hRI : RiemannIndexFormula K F) (T : Finset (Place K F)) (t : Place K F) :
    LSpace (pointDivisor T - Finsupp.single t 1) < LSpace (pointDivisor T) := by
  classical
  refine lt_of_le_of_ne (lSpace_mono (punctureDivisor_sub_single_le T t)) ?_
  intro heq
  have h1 : (ell (pointDivisor T) : ℤ)
      = Divisor.degree (pointDivisor T) + 1 - (genus K F : ℤ) :=
    H1VanishingData.ell_eq_degree_add_one (K := K) (F := F) hD hRI _
  have h2 : (ell (pointDivisor T - Finsupp.single t 1) : ℤ)
      = Divisor.degree (pointDivisor T - Finsupp.single t 1) + 1 - (genus K F : ℤ) :=
    H1VanishingData.ell_eq_degree_add_one (K := K) (F := F) hD hRI _
  have hdeg : Divisor.degree (pointDivisor T - Finsupp.single t 1)
      = Divisor.degree (pointDivisor T) - 1 := by
    rw [map_sub, Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed t]
    norm_num
  have heq' : (ell (pointDivisor T - Finsupp.single t 1) : ℤ)
      = (ell (pointDivisor T) : ℤ) :=
    congrArg (fun s : Submodule K F => (Module.finrank K s : ℤ)) heq
  rw [hdeg] at h2
  linarith

end H1

/-! ### (obligation: A3-EVAL-MAPS)  `s1` via the B2 evaluation lemma

`Mzk1G1A3EvaluationActual.exists_forall_apply_ne_zero` (PROVED, axiom-clean) produces a section
nonzero at every point of `T` **given** a nonzero evaluation map at each point.  Precise
missing input (same `AlgebraicCurve` API in both roots):

    EvaluationMapsAvailable D T :=
      ∃ (κ : Place K F → Type) (_ : ∀ p : Place K F, Field (κ p))
        (_ : ∀ p : Place K F, Algebra K (κ p))
        (ev : ∀ p : Place K F, LSpace D →ₗ[K] κ p), ∀ t ∈ T, ev t ≠ 0

from which the lemma gives `∃ s : LSpace D, ∀ t ∈ T, ev t s ≠ 0`.  Producing `ev t ≠ 0` for
`t ∈ T` is registered obligation (i) of the A3 file (Serre duality: `H¹(O(D - t)) = 0` implies
evaluation at `t` is surjective).  This file does NOT depend on it: the §6.2 `s1` below is the
one built by the PROVED Riemann–Roch producer `zero_divisor_exists_proved`. -/


/-! ## Part 3. The protected-point data and its §6.2 properties -/

/-- The `psi`-fibre over `0`, as a set of places: the zeros of `psi`. -/
def fiberAboveZero (psi : F) : Set (Place K F) := {p | 0 < p.ord psi}

/-- `psi` is unramified over `0`: every point of the fibre over `0` is a simple zero.  This
is the explicit ord-characterization of `0 ∉ Branch psi` for the map to `P¹`. -/
def unramifiedOverZero (psi : F) : Prop := ∀ p : Place K F, 0 < p.ord psi → p.ord psi = 1

/-- `0` is not a branch value of `psi` (explicit characterization). -/
def zeroNotBranch (psi : F) : Prop := unramifiedOverZero (K := K) (F := F) psi

/-- The §6.2 protected-point package: actual point sets `S`, `T`, the actual reduced effective divisor
`D`, the two sections of `O(D)` and `psi = [s0 : s1]` with its three properties. -/
structure ProtectedPointData (K F : Type*) [Field K] [Field F] [Algebra K F] where
  S : Finset (Place K F)
  T : Finset (Place K F)
  D : Divisor K F
  s0 : F
  s1 : F
  psi : F
  h_S_notMem_T : ∀ s ∈ S, s ∉ T
  h_T_subset_supp : (↑T : Set (Place K F)) ⊆ suppSet D
  h_supp_subset_T : suppSet D ⊆ (↑T : Set (Place K F))
  h_supp_disjoint_S : Disjoint (suppSet D) (↑S : Set (Place K F))
  h_effective : ∀ p : Place K F, 0 ≤ D p
  h_reduced : ∀ p : Place K F, D p ≤ 1
  h_s0_ne : s0 ≠ 0
  h_s1_ne : s1 ≠ 0
  h_div_s0 : ∀ p : Place K F, sectionOrder D s0 p = D p
  h_s1_nonzero_on_D : ∀ p : Place K F, D p ≠ 0 → sectionOrder D s1 p = 0
  h_psi_eq : psi = s0 / s1
  h_psi_zeros : ∀ p : Place K F, 0 < p.ord psi ↔ D p ≠ 0
  h_psi_away_S : ∀ s ∈ S, ¬ 0 < s.ord psi
  h_psi_unramified_zero : unramifiedOverZero (K := K) (F := F) psi
  h_D_galois : ∀ σ : F ≃ₐ[K] F, σ • D = D

namespace ProtectedPointData

variable (P : ProtectedPointData K F)

/-- (i) `T ⊆ supp D`. -/
theorem t_subset_supp : (↑P.T : Set (Place K F)) ⊆ suppSet P.D := P.h_T_subset_supp

/-- (ii) `supp D ∩ S = ∅`. -/
theorem supp_disjoint_S : Disjoint (suppSet P.D) (↑P.S : Set (Place K F)) :=
  P.h_supp_disjoint_S

/-- The support of `D` is exactly `T`. -/
theorem supp_eq_T : suppSet P.D = (↑P.T : Set (Place K F)) :=
  Set.Subset.antisymm P.h_supp_subset_T P.h_T_subset_supp

/-- `D` is effective and reduced. -/
theorem effective_and_reduced :
    (∀ p : Place K F, 0 ≤ P.D p) ∧ (∀ p : Place K F, P.D p ≤ 1) :=
  ⟨P.h_effective, P.h_reduced⟩

/-- (iii) The divisor of the `O(D)`-section `s0` is `D`. -/
theorem div_s0 : ∀ p : Place K F, sectionOrder P.D P.s0 p = P.D p := P.h_div_s0

/-- (iii) `s1` does not vanish on `D`. -/
theorem s1_nonzero_on_D : ∀ p : Place K F, P.D p ≠ 0 → sectionOrder P.D P.s1 p = 0 :=
  P.h_s1_nonzero_on_D

/-- (iv) `psi⁻¹(0) = supp D`: the fibre of `psi` over `0` is the support of `D`. -/
theorem fiber_zero_eq_supp :
    fiberAboveZero (K := K) (F := F) P.psi = suppSet P.D := by
  ext p
  rw [fiberAboveZero, Set.mem_setOf_eq, mem_suppSet]
  exact P.h_psi_zeros p

/-- (iv) `0 ∉ psi(S)`: no point of `S` maps to `0`. -/
theorem fiber_zero_disjoint_S :
    Disjoint (fiberAboveZero (K := K) (F := F) P.psi) (↑P.S : Set (Place K F)) := by
  rw [fiberAboveZero, Set.disjoint_left]
  intro a ha hb
  exact P.h_psi_away_S a hb ha

/-- (iv) `0 ∉ Branch psi` (explicit characterization: all zeros of `psi` are simple). -/
theorem zero_not_branch : zeroNotBranch (K := K) (F := F) P.psi := P.h_psi_unramified_zero

/-- **§6.2 (iv), consolidated**: `psi⁻¹(0) = supp D`, `0 ∉ psi(S)`, and `0 ∉ Branch psi`
(i.e. all zeros of `psi` are simple). -/
theorem psi_structure :
    fiberAboveZero (K := K) (F := F) P.psi = suppSet P.D ∧
      (∀ s ∈ P.S, ¬ 0 < s.ord P.psi) ∧ zeroNotBranch (K := K) (F := F) P.psi :=
  ⟨P.fiber_zero_eq_supp, P.h_psi_away_S, P.zero_not_branch⟩

/-- Galois invariance of the protected divisor. -/
theorem D_galois_invariant (σ : F ≃ₐ[K] F) : σ • P.D = P.D := P.h_D_galois σ

/-- Consumer-facing alias for `psi⁻¹(0) = supp D` (`fiber_zero_eq_supp`). -/
theorem psi_inv_zero :
    fiberAboveZero (K := K) (F := F) P.psi = suppSet P.D :=
  P.fiber_zero_eq_supp

/-- Consumer-facing alias for `0 ∉ psi(S)` (`fiber_zero_disjoint_S`). -/
theorem zero_notin_psi_S :
    Disjoint (fiberAboveZero (K := K) (F := F) P.psi) (↑P.S : Set (Place K F)) :=
  P.fiber_zero_disjoint_S

end ProtectedPointData

/-! ## Part 3b. The A3 evaluation maps (obligation A3-EVAL-MAPS) and the B2 evaluation lemma -/

/-- **Obligation A3-EVAL-MAPS (paper §4.2 L251–261, route L257).**  The evaluation maps of the
sections of `O(D)` at the places of `K/F`: for each place `p` a `K`-linear map `ev p` from the
section space `LSpace D` to a residue field `κ p`, vanishing exactly on the sections that vanish
at `p`.  Producing this data for `D = pointDivisor T` is the Serre-duality corollary
`H¹(O(D - [p])) = 0 ⇒ ev_p` surjective (registered obligation (i) of
`Mzk1G1A3EvaluationActual`).  This file does NOT assume such data exists: the type below is the
precise residual. -/
structure A3EvalMaps (D : Divisor K F) (κ : Place K F → Type)
    [∀ p : Place K F, Field (κ p)] [∀ p : Place K F, Algebra K (κ p)] where
  /-- evaluation of a section at a place. -/
  ev : ∀ p : Place K F, LSpace D →ₗ[K] κ p
  /-- the kernel of evaluation is exactly "the section vanishes at `p`". -/
  ev_eq_zero_iff : ∀ (p : Place K F) (s : LSpace D),
    ev p s = 0 ↔ 0 < sectionOrder D (s : F) p

/-- **The B2 evaluation lemma applied to section spaces.**  Over an infinite base field, finitely
many nonzero evaluation maps cannot annihilate every section: there is `s1` on which every
`ev t`, `t ∈ T`, is nonzero.  (Donor: `Mzk1G1A3EvaluationActual.exists_forall_apply_ne_zero`.) -/
theorem A3EvalMaps.exists_section_ne_zero [Infinite K] {D : Divisor K F}
    {κ : Place K F → Type} [∀ p : Place K F, Field (κ p)]
    [∀ p : Place K F, Algebra K (κ p)]
    (E : A3EvalMaps (K := K) (F := F) D κ) (T : Finset (Place K F))
    (hnev : ∀ t ∈ T, E.ev t ≠ 0) :
    ∃ s1 : LSpace D, ∀ t ∈ T, E.ev t s1 ≠ 0 :=
  LeanFormal.IUT.XiFPaper.Mzk1G1A3EvaluationActual.exists_forall_apply_ne_zero
    (k := K) (V := LSpace D) T κ E.ev hnev

/-- A section of `O(D)` that is not in `O(D - [p])` does not vanish at `p`: its order at `p` is
exactly `-D p`, so `sectionOrder D s p ≤ 0`. -/
theorem not_lt_sectionOrder_of_notMem_sub_single {D : Divisor K F} {p : Place K F} {f : F}
    (hD : f ∈ LSpace D) (hnot : f ∉ LSpace (D - Finsupp.single p 1)) :
    ¬ (0 < sectionOrder D f p) := by
  intro hpos
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hnot (LSpace (D - Finsupp.single p 1)).zero_mem
  have hDf : ∀ v : Place K F, -D v ≤ v.ord f :=
    (mem_lSpace_iff_ord.mp hD).resolve_left hf0
  apply hnot
  rw [mem_lSpace_iff_ord]
  refine Or.inr fun v => ?_
  by_cases hvp : v = p
  · subst hvp
    have hsingle : Finsupp.single p (1 : ℤ) p = 1 := Finsupp.single_eq_same
    rw [Finsupp.sub_apply, hsingle]
    have hpos' : 0 < p.ord f + D p := by simpa [sectionOrder] using hpos
    linarith
  · have hsingle : Finsupp.single p (1 : ℤ) v = 0 := by
      exact Finsupp.single_eq_of_ne (h := hvp)
    rw [Finsupp.sub_apply, hsingle, sub_zero]
    exact hDf v

/-! ## Part 4. §6.3 ratio-inversion glue data for the section-dependent cover -/

theorem ratio_inverse (s0 s1 : F) : (s0 / s1)⁻¹ = s1 / s0 :=
  inv_div s0 s1

theorem ratio_mul_inverse {s0 s1 : F} (h0 : s0 ≠ 0) (h1 : s1 ≠ 0) :
    (s0 / s1) * (s1 / s0) = 1 := by
  rw [div_mul_div_comm, mul_comm s1 s0]
  exact div_self (mul_ne_zero h0 h1)

/-- On `D(s1)` the map is read off from `s0 / s1`; on `D(s0)` from its inverse `s1 / s0`.
The two readings agree as ratios of the same section pair. -/
theorem psi_ratio_cover (P : ProtectedPointData K F) :
    P.psi = P.s0 / P.s1 ∧ (P.s1 / P.s0) = (P.s0 / P.s1)⁻¹ :=
  ⟨P.h_psi_eq, (ratio_inverse P.s0 P.s1).symm⟩

/-! ## Part 5. The producer: protected point data from Riemann–Roch -/

section Main

variable [IsAlgClosed K] [Infinite K] [DecidableEq (RatFunc K)]
  [HasCanonicalDivisor (K := K) (F := F)]
  [∀ w : Place K F, w.DCoordGenerates]
  [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
  [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
  [HasLocalResidue K F] [∀ w : Place K F, w.FiniteResidue] [Nontrivial Ω[F⁄K]]
  [IsCurveOver K F] [IsCurveOver K (RatFunc K)]
  [∀ u : Place K (RatFunc K), u.FiniteResidue]
  [HasCanonicalLocalResidueKStar K F] [HasPrincipalDivisors K F]
  [Algebra.IsSeparable (RatFunc K) F]
  [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : Place K (RatFunc K), v.DCoordGenerates]
  [FiniteDimensional (RatFunc K) F] [HasSeparableResidue K F]

/-- **R4 producer (§6.2).**  For any finite `T` with `2g+1 ≤ #T` and any finite `S` disjoint from `T`,
with `T` Galois stable, there are `D = Σ_{t ∈ T} [t]` and sections `s0, s1`, `psi = s0/s1` satisfying
(i) `T ⊆ supp D`, (ii) `supp D ∩ S = ∅`, (iii) `div s0 = D` and `s1` nonzero on `D`,
(iv) `psi⁻¹(0) = supp D` and `0 ∉ psi(S) ∪ Branch psi`. -/
theorem protectedPointData_exists (S T : Finset (Place K F))
    (hcard : 2 * genus K F + 1 ≤ T.card) (hS : ∀ s ∈ S, s ∉ T)
    (hTgal : GaloisStable (K := K) (F := F) T) :
    ∃ P : ProtectedPointData K F, P.S = S ∧ P.T = T ∧ P.D = pointDivisor T := by
  classical
  obtain ⟨g, hg0, hzeros, hsimple⟩ :=
    zero_divisor_exists_proved (K := K) (F := F) T hcard
  have hdiv0 : ∀ p : Place K F,
      sectionOrder (pointDivisor T) (1 : F) p = pointDivisor T p := by
    intro p
    rw [sectionOrder, Place.ord_one, zero_add]
  have hs1nz : ∀ p : Place K F, pointDivisor T p ≠ 0 →
      sectionOrder (pointDivisor T) (g⁻¹) p = 0 := by
    intro p hp
    have hpT : p ∈ T := pointDivisor_apply_ne_zero_iff.mp hp
    have hDp : pointDivisor T p = 1 := pointDivisor_apply_of_mem hpT
    have hpord : p.ord g = 1 := hsimple p hpT
    rw [sectionOrder, hDp, Place.ord_inv, hpord]
    norm_num
  have hpsieq : g = (1 : F) / g⁻¹ := by
    rw [one_div, inv_inv]
  have hpsizero : ∀ p : Place K F, 0 < p.ord g ↔ pointDivisor T p ≠ 0 := by
    intro p
    rw [pointDivisor_apply_ne_zero_iff]
    exact hzeros p
  have hpsiS : ∀ s ∈ S, ¬ 0 < s.ord g := by
    intro s hsS hpos
    exact hS s hsS ((hzeros s).mp hpos)
  have hpsiunram : unramifiedOverZero (K := K) (F := F) g := by
    intro p hp
    exact hsimple p ((hzeros p).mp hp)
  let hP : ProtectedPointData K F :=
    { S := S
      T := T
      D := pointDivisor T
      s0 := 1
      s1 := g⁻¹
      psi := g
      h_S_notMem_T := hS
      h_T_subset_supp := pointDivisor_subset_supp T
      h_supp_subset_T := pointDivisor_supp_subset T
      h_supp_disjoint_S := pointDivisor_disjoint_of_notMem hS
      h_effective := pointDivisor_effective T
      h_reduced := pointDivisor_reduced T
      h_s0_ne := one_ne_zero
      h_s1_ne := inv_ne_zero hg0
      h_div_s0 := hdiv0
      h_s1_nonzero_on_D := hs1nz
      h_psi_eq := hpsieq
      h_psi_zeros := hpsizero
      h_psi_away_S := hpsiS
      h_psi_unramified_zero := hpsiunram
      h_D_galois := pointDivisor_galois_invariant hTgal }
  refine ⟨hP, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl

/-- **R4 size input** at `n = 2g+1`: the protected set can be taken of size `≥ 2g+1` and
disjoint from `S` (`T` itself qualifies). -/
theorem protectedPointData_size_exists (S T : Finset (Place K F))
    (hcard : 2 * genus K F + 1 ≤ T.card) (hS : ∀ s ∈ S, s ∉ T) :
    ∃ T' : Finset (Place K F), T ⊆ T' ∧ 2 * genus K F + 1 ≤ T'.card ∧ Disjoint T' S :=
  exists_superset_card_disjoint (2 * genus K F + 1) S T hcard hS

/-- **Size input with degree**, at `n = 2g+1`: the enlarged set `T'` also carries the exact degree
form `deg (pointDivisor T') = #T'`. -/
theorem protectedPointData_size_exists_deg (S T : Finset (Place K F))
    (hcard : 2 * genus K F + 1 ≤ T.card) (hS : ∀ s ∈ S, s ∉ T) :
    ∃ T' : Finset (Place K F), T ⊆ T' ∧ 2 * genus K F + 1 ≤ T'.card ∧ Disjoint T' S ∧
      Divisor.degree (pointDivisor T') = (T'.card : ℤ) :=
  exists_superset_card_disjoint_deg (2 * genus K F + 1) S T hcard hS

/-- **The `s1` selector via the A3 evaluation lemma (§4.2).**  From `H1VanishingData` (through the
strict drop `L(D - [t]) < L(D)`) and the A3 evaluation maps, there is a section `s1` of `O(D)`
that does not vanish at any point of `T`; equivalently `sectionOrder D s1 t = 0` on `T`. -/
theorem exists_s1_nonzero_on_of_h1 (T : Finset (Place K F)) (hT : T.Nonempty)
    {κ : Place K F → Type} [∀ p : Place K F, Field (κ p)]
    [∀ p : Place K F, Algebra K (κ p)]
    (hD : H1VanishingData K F) (hRI : RiemannIndexFormula K F)
    (E : A3EvalMaps (K := K) (F := F) (pointDivisor T) κ) :
    ∃ s1 : LSpace (pointDivisor T), (s1 : F) ≠ 0 ∧
      ∀ t ∈ T, sectionOrder (pointDivisor T) (s1 : F) t = 0 := by
  classical
  have hproper : ∀ t ∈ T,
      LSpace (pointDivisor T - Finsupp.single t 1) < LSpace (pointDivisor T) :=
    fun t _ => H1VanishingData.lSpace_sub_single_lt (K := K) (F := F) hD hRI T t
  obtain ⟨s₀, hs₀D, hs₀not⟩ :=
    exists_mem_notMem_of_proper T (fun t => LSpace (pointDivisor T - Finsupp.single t 1))
      (LSpace (pointDivisor T)) hproper
  have hnev : ∀ t ∈ T, E.ev t ≠ 0 := by
    intro t ht h0
    have hz : E.ev t ⟨s₀, hs₀D⟩ = 0 := by simp [h0]
    exact not_lt_sectionOrder_of_notMem_sub_single hs₀D (hs₀not t ht)
      ((E.ev_eq_zero_iff t ⟨s₀, hs₀D⟩).mp hz)
  obtain ⟨s1, hs1⟩ := E.exists_section_ne_zero T hnev
  have hs1ne : (s1 : F) ≠ 0 := by
    obtain ⟨t, ht⟩ := hT
    intro h0
    have hz : s1 = 0 := Subtype.ext h0
    exact hs1 t ht (by rw [hz]; simp)
  refine ⟨s1, hs1ne, fun t ht => ?_⟩
  have hge : 0 ≤ sectionOrder (pointDivisor T) (s1 : F) t := by
    have hmem := (mem_lSpace_iff_ord.mp s1.2).resolve_left hs1ne
    have h := hmem t
    show 0 ≤ t.ord (s1 : F) + pointDivisor T t
    linarith
  have hnlt : ¬ (0 < sectionOrder (pointDivisor T) (s1 : F) t) :=
    fun hpos => hs1 t ht ((E.ev_eq_zero_iff t s1).mpr hpos)
  omega

/-- **R4 producer (§6.2) via H¹ vanishing.**  From the R4 H¹-vanishing package (with the
Riemann-index formula) and the A3 evaluation maps, for any finite `T` with `2g+1 ≤ #T` and any
finite `S` avoiding `T`: `D = Σ_{t∈T} [t]`, `s0 = 1`, `s1` nonzero on `D` (from the evaluation
lemma), `psi = s0/s1 = s1⁻¹` with simple zeros exactly `supp D`, no point of `S` over `0`, and
Galois invariance.  Residual: the evaluation maps (obligation A3-EVAL-MAPS). -/
theorem protectedPointData_exists_of_h1 (S T : Finset (Place K F))
    {κ : Place K F → Type} [∀ p : Place K F, Field (κ p)]
    [∀ p : Place K F, Algebra K (κ p)]
    (hD : H1VanishingData K F) (hRI : RiemannIndexFormula K F)
    (E : A3EvalMaps (K := K) (F := F) (pointDivisor T) κ)
    (hcard : 2 * genus K F + 1 ≤ T.card) (hS : ∀ s ∈ S, s ∉ T)
    (hTgal : GaloisStable (K := K) (F := F) T) :
    ∃ P : ProtectedPointData K F, P.S = S ∧ P.T = T ∧ P.D = pointDivisor T := by
  classical
  have hTpos : 0 < T.card := by omega
  have hTne : T.Nonempty := Finset.card_pos.mp hTpos
  obtain ⟨s1, hs1ne, hsec⟩ := exists_s1_nonzero_on_of_h1 T hTne hD hRI E
  have hord_one : ∀ p : Place K F, p ∈ T → p.ord (s1 : F) = -1 := by
    intro p hp
    have hsec' : p.ord (s1 : F) + pointDivisor T p = 0 := hsec p hp
    have hpD : pointDivisor T p = 1 := pointDivisor_apply_of_mem hp
    rw [hpD] at hsec'
    linarith
  have hord_nn : ∀ p : Place K F, p ∉ T → 0 ≤ p.ord (s1 : F) := by
    intro p hp
    have hmem := (mem_lSpace_iff_ord.mp s1.2).resolve_left hs1ne
    have hpD : pointDivisor T p = 0 := pointDivisor_apply_of_notMem hp
    simpa [hpD] using hmem p
  let psi : F := (1 : F) / (s1 : F)
  have hord_psi : ∀ p : Place K F, p.ord psi = -p.ord (s1 : F) := by
    intro p
    simp only [psi, one_div, Place.ord_inv]
  have hpsi_zeros : ∀ p : Place K F, 0 < p.ord psi ↔ pointDivisor T p ≠ 0 := by
    intro p
    constructor
    · intro hpos hD0
      have hpT : p ∉ T := by
        intro hpT
        rw [pointDivisor_apply_of_mem hpT] at hD0
        exact one_ne_zero hD0
      have hge : 0 ≤ p.ord (s1 : F) := hord_nn p hpT
      rw [hord_psi] at hpos
      linarith
    · intro hne
      have hpT : p ∈ T := pointDivisor_apply_ne_zero_iff.mp hne
      rw [hord_psi, hord_one p hpT]
      norm_num
  have hpsi_awayS : ∀ s ∈ S, ¬ 0 < s.ord psi := by
    intro s hsS hpos
    exact hS s hsS (pointDivisor_apply_ne_zero_iff.mp ((hpsi_zeros s).mp hpos))
  have hpsi_unram : unramifiedOverZero (K := K) (F := F) psi := by
    intro p hp
    have hpT : p ∈ T := pointDivisor_apply_ne_zero_iff.mp ((hpsi_zeros p).mp hp)
    rw [hord_psi, hord_one p hpT]
    norm_num
  have hdiv0 : ∀ p : Place K F,
      sectionOrder (pointDivisor T) (1 : F) p = pointDivisor T p := by
    intro p
    rw [sectionOrder, Place.ord_one, zero_add]
  have hpsieq : psi = (1 : F) / (s1 : F) := rfl
  let hP : ProtectedPointData K F :=
    { S := S,
      T := T,
      D := pointDivisor T,
      s0 := 1,
      s1 := (s1 : F),
      psi := psi,
      h_S_notMem_T := hS,
      h_T_subset_supp := pointDivisor_subset_supp T,
      h_supp_subset_T := pointDivisor_supp_subset T,
      h_supp_disjoint_S := pointDivisor_disjoint_of_notMem hS,
      h_effective := pointDivisor_effective T,
      h_reduced := pointDivisor_reduced T,
      h_s0_ne := one_ne_zero,
      h_s1_ne := hs1ne,
      h_div_s0 := hdiv0,
      h_s1_nonzero_on_D := fun p hp => hsec p (pointDivisor_apply_ne_zero_iff.mp hp),
      h_psi_eq := hpsieq,
      h_psi_zeros := hpsi_zeros,
      h_psi_away_S := hpsi_awayS,
      h_psi_unramified_zero := hpsi_unram,
      h_D_galois := pointDivisor_galois_invariant hTgal }
  refine ⟨hP, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · simp only [hP]

end Main

/-! ## Part 6. Bundle form of the producer (the Fermat wiring hook) -/

/-- The producer with the Riemann–Roch bundle passed explicitly, so that a single term
`RRAvailable K F` (obligation: FERMAT-FUNCTION-FIELD-BUNDLE, for the function field of `Y_n`)
suffices to run it.  The genus in the degree hypothesis is the genus attached to the bundle's
canonical divisor. -/
theorem protectedPointData_exists_of_bundle (bundle : RRAvailable K F)
    (S T : Finset (Place K F))
    (hcard : 2 * @genus K F _ _ _ bundle.hasCanonicalDivisor + 1 ≤ T.card)
    (hS : ∀ s ∈ S, s ∉ T)
    (hTgal : GaloisStable (K := K) (F := F) T) :
    ∃ P : ProtectedPointData K F, P.S = S ∧ P.T = T ∧ P.D = pointDivisor T := by
  letI := bundle.isAlgClosed
  letI := bundle.infinite
  letI := bundle.decEqRatFunc
  letI := bundle.hasCanonicalDivisor
  letI := bundle.dCoordGenerates_places
  letI := bundle.algebraRatFunc
  letI := bundle.isScalarTower
  letI := bundle.isIntegral
  letI := bundle.moduleFinite
  letI := bundle.hasLocalResidue
  letI := bundle.finiteResidue_places
  letI := bundle.nontrivialOmega
  letI := bundle.isCurveOver
  letI := bundle.isCurveOverRatFunc
  letI := bundle.finiteResidue_ratFunc
  letI := bundle.hasCanonicalLocalResidueKStar
  letI := bundle.hasPrincipalDivisors
  letI := bundle.isSeparable
  letI := bundle.nontrivialOmegaRatFunc
  letI := bundle.dCoordGenerates_ratFunc
  letI := bundle.finiteDimensional
  letI := bundle.hasSeparableResidue
  exact protectedPointData_exists S T (by simpa using hcard) hS hTgal

/-! ## Part 7. Rows (diagnostic table, in-project convention) -/

/-- Diagnostic rows: what is proved here and what is not. -/
def r4Rows : List (String × String × String) :=
  [ ("S, T actual finite point sets", "DEF + PROVED finite (Finset (Place K F))", "protectedPointData_exists")
  , ("D actual reduced effective divisor", "PROVED (pointDivisor_effective/reduced)", "D = pointDivisor T = Σ_{t∈T} [t]")
  , ("T ⊆ supp D", "PROVED (pointDivisor_subset_supp, supp_eq_T)", "pointDivisor_support")
  , ("supp D ∩ S = ∅", "PROVED (pointDivisor_disjoint_of_notMem)", "from S ∩ T = ∅")
  , ("Galois stability of T (explicit orbit-union char.)", "DEF GaloisStable + PROVED σ • D = D", "pointDivisor_galois_invariant")
  , ("sections s0, s1 of O(D): div s0 = D, s1 ≠ 0 on D", "PROVED from RR (zero_divisor_exists_proved)", "s0 = 1, s1 = g⁻¹")
  , ("psi = [s0 : s1] = s0/s1 = g, psi⁻¹(0) = supp D", "PROVED (fiber_zero_eq_supp)", "h_psi_zeros")
  , ("0 ∉ psi(S)", "PROVED (fiber_zero_disjoint_S)", "h_psi_away_S")
  , ("0 ∉ Branch psi", "PROVED (zero_not_branch: all zeros simple)", "h_psi_unramified_zero; explicit ord char.")
  , ("§6.3 ratio-inversion glue on D(s1) / D(s0)", "PROVED (ratio_inverse/ratio_mul_inverse/psi_ratio_cover)", "section-dependent cover data")
  , ("H¹-vanishing bundle H1VanishingData (4 fields, ported FLT props)", "STRUCT + PROVED consumption (indexFormula, ell_eq_degree_add_one, weilDuality)", "h1_vanish / ConstantsAreBase consumed by size-H¹ packing")
  , ("size existence: T ⊆ T', 2g+1 ≤ #T', Disjoint T' S", "PROVED (exists_superset_card_disjoint; T' = T suffices)", "protectedPointData_size_exists (genus form)")
  , ("s1 via B2 evaluation lemma exists_forall_apply_ne_zero", "PROVED conditional on A3EvalMaps (evaluation maps = obligation A3-EVAL-MAPS)", "A3EvalMaps.exists_section_ne_zero, exists_s1_nonzero_on_of_h1")
  , ("H¹ vanishing ⇒ L(D-[t]) < L(D) (strict drop at a point)", "PROVED (H1VanishingData.lSpace_sub_single_lt)", "consumes h1_vanish via ell_eq_degree_add_one")
  , ("§6.2 producer via H¹ + A3 evaluation (s0 = 1, psi = 1/s1, zeros exactly supp D)", "PROVED conditional on A3EvalMaps (obligation A3-EVAL-MAPS)", "protectedPointData_exists_of_h1")
  , ("size form with degree: deg (pointDivisor T') = #T'", "PROVED (degree_pointDivisor)", "exists_superset_card_disjoint_deg, protectedPointData_size_exists_deg")
  , ("RRAvailable bundle for F_n = function field of Y_n", "OBLIGATION FERMAT-FUNCTION-FIELD-BUNDLE (no inhabitant)", "protectedPointData_exists_of_bundle consumes it")
  , ("scheme-level S, T ⊂ fermatCurveScheme n", "OBLIGATION (not formalized: scheme-point ↔ Place bridge)", "no fake; see docstring")
  , ("§6.2 (i)–(iv) consolidated interface", "PROVED (psi_structure; aliases psi_inv_zero / zero_notin_psi_S)", "fiber_zero_eq_supp + h_psi_away_S + zero_not_branch")
  ]

theorem r4Rows_length : r4Rows.length = 19 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.pointDivisor_support
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.pointDivisor_galois_invariant
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.protectedPointData_exists
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.ProtectedPointData.fiber_zero_eq_supp
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.ProtectedPointData.zero_not_branch
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.ratio_mul_inverse
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.protectedPointData_exists_of_bundle
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.exists_superset_card_disjoint
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.protectedPointData_size_exists
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.H1VanishingData.indexFormula
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.H1VanishingData.ell_eq_degree_add_one
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.H1VanishingData.weilDuality
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.ProtectedPointData.psi_structure
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.degree_pointDivisor
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.exists_superset_card_disjoint_deg
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.H1VanishingData.lSpace_sub_single_lt
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.A3EvalMaps.exists_section_ne_zero
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.not_lt_sectionOrder_of_notMem_sub_single
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.exists_s1_nonzero_on_of_h1
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.protectedPointData_exists_of_h1
#print axioms LeanFormal.IUT.XiFPaper.Mzk1G1R4ProtectedActual.protectedPointData_size_exists_deg