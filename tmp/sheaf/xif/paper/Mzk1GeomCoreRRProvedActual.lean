import tmp.sheaf.xif.paper.Mzk1RRProvedActual
import tmp.external.ported.flt_core.Theorems.Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg
import Mathlib.GroupTheory.CosetCover

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: RR PROVED (qpilot Mzk1RRProvedActual: flt_core REAL port, functionFieldRiemannRoch_proved) + flt_core ell_eq_zero_of_degree_neg / canonicalDivisorOf / genus / IsCurveOver.deg_eq_one_of_isAlgClosed + Pencil base layer (PencilData construction, punctureDivisor) -> MIGRATE D function-field foundation to flt_core root; DISCHARGE hRR and hdual.

# Mzk1GeomCoreRRProvedActual — Problem D foundation on the flt_core root, RR PROVED

Migrates the D function-field foundation from the flt_test root (legacy) to the
self-contained flt_core root, where the two former named inputs are DISCHARGED:
* hRR -> Mzk1RRProvedActual.functionFieldRiemannRoch_proved (ported closure; axioms trio);
* hdual -> flt_core ell_eq_zero_of_degree_neg at the canonical divisor:
  deg K <= 2g-1 (canonical_degree_le_two_genus, PROVED from the rounded genus definition)
  and |T| >= 2g+1 give deg(K - D) < 0 and deg(K - (D - t)) < 0, so both dual terms vanish.
Then the pencil construction (h in L(D) outside every L(D - t), g = h^{-1}) is adapted
to the flt_core API: `zero_divisor_exists_proved` gives g != 0 with ORD(g) = +1 exactly
on T and ORD(g) <= 0 outside T (zero divisor exactly sum_T [t]).

LEGACY: flt_test-root Mzk1GeomCoreFoundationActual stays as legacy (flt_test and flt_core
cannot be imported in the same file: duplicate AlgebraicCurve definitions).  The
scheme-level layer (FibreOverZeroEq/MapsTToZeroOn/consumer chain) stays in the legacy
root because Mzk1FiniteMapData lives in the flt_th tree.
Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCoreRRProvedActual

universe u

open KaehlerDifferential

/-! ## PART 1: base pencil layer (flt_core API, RR-independent) -/

section BaseLayer

theorem ell_drop_of_rr {g ellD ellDt ellKD ellKDt degD : ℤ}
    (h1 : ellD - ellKD = degD + 1 - g)
    (h2 : ellDt - ellKDt = (degD - 1) + 1 - g)
    (v1 : ellKD = 0) (v2 : ellKDt = 0) : ellD - ellDt = 1 := by
  omega

theorem exists_mem_notMem_of_proper {K V : Type*} [Field K] [Infinite K]
    [AddCommGroup V] [Module K V] {ι : Type*} (s : Finset ι)
    (W : ι → Submodule K V) (U : Submodule K V) (h : ∀ i ∈ s, W i < U) :
    ∃ v ∈ U, ∀ i ∈ s, v ∉ W i := by
  classical
  set W' : ι → Submodule K U := fun i => Submodule.comap U.subtype (W i) with hW'
  have htop : (⊤ : Submodule K U) ∉ s.image W' := by
    intro hmem
    obtain ⟨i, hi, hWi⟩ := Finset.mem_image.mp hmem
    have hle : U ≤ W i := Submodule.comap_subtype_eq_top.mp hWi
    exact (not_le_of_gt (h i hi)) hle
  have hne : (⋃ p ∈ s.image W', (p : Set U)) ≠ Set.univ :=
    Subspace.biUnion_ne_univ_of_top_notMem htop
  obtain ⟨v, hv⟩ : ∃ v : U, v ∉ ⋃ p ∈ s.image W', (p : Set U) := by
    by_contra hc
    push Not at hc
    exact hne (Set.eq_univ_of_forall hc)
  refine ⟨(v : V), v.2, fun i hi hvi => ?_⟩
  have hmemW : v ∈ W' i := by
    rw [hW', Submodule.mem_comap]
    exact hvi
  exact hv (Set.mem_biUnion (Finset.mem_image_of_mem W' hi) hmemW)

structure PencilData (K F P : Type*) [Field K] [Field F] [Algebra K F] where
  ord : P → F → ℤ
  T : Finset P
  LD : Submodule K F
  LDt : P → Submodule K F
  proper : ∀ t ∈ T, LDt t < LD
  pole : ∀ h ∈ LD, ∀ t ∈ T, h ∉ LDt t → ord t h = -1
  regular : ∀ h ∈ LD, h ≠ 0 → ∀ p, p ∉ T → 0 ≤ ord p h
  ord_inv : ∀ p (h : F), h ≠ 0 → ord p h⁻¹ = -ord p h

theorem exists_simple_pole_function {K F P : Type*} [Field K] [Infinite K] [Field F]
    [Algebra K F] (X : PencilData K F P) (hT : X.T.Nonempty) :
    ∃ h ∈ X.LD, h ≠ 0 ∧ (∀ t ∈ X.T, X.ord t h = -1) ∧
      ∀ p, p ∉ X.T → 0 ≤ X.ord p h := by
  obtain ⟨v, hvU, hvW⟩ := exists_mem_notMem_of_proper X.T X.LDt X.LD X.proper
  have hv0 : v ≠ 0 := by
    obtain ⟨t, ht⟩ := hT
    intro h0
    exact hvW t ht (by rw [h0]; exact (X.LDt t).zero_mem)
  exact ⟨v, hvU, hv0, fun t ht => X.pole v hvU t ht (hvW t ht),
    fun p hp => X.regular v hvU hv0 p hp⟩

theorem exists_function_with_zero_divisor {K F P : Type*} [Field K] [Infinite K]
    [Field F] [Algebra K F] (X : PencilData K F P) (hT : X.T.Nonempty) :
    ∃ g : F, g ≠ 0 ∧ (∀ t ∈ X.T, X.ord t g = 1) ∧
      ∀ p, p ∉ X.T → X.ord p g ≤ 0 := by
  obtain ⟨h, hhLD, hh0, hpole, hreg⟩ := exists_simple_pole_function X hT
  refine ⟨h⁻¹, inv_ne_zero hh0, fun t ht => ?_, fun p hp => ?_⟩
  · rw [X.ord_inv t h hh0, hpole t ht]
    norm_num
  · rw [X.ord_inv p h hh0]
    linarith [hreg p hp]

end BaseLayer

/-! ## PART 2: flt_core ported API — puncture divisor, its degree, canonical bound -/

section PortedAPI

open AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def punctureDivisor (T : Finset (Place K F)) : Divisor K F :=
  ∑ t ∈ T, Finsupp.single t (1 : ℤ)

theorem punctureDivisor_apply_of_mem {T : Finset (Place K F)} {v : Place K F}
    (hv : v ∈ T) : punctureDivisor T v = 1 := by
  classical
  have h : ∀ t ∈ T, Finsupp.single t (1 : ℤ) v = (if t = v then (1 : ℤ) else 0) := by
    intro t _
    rw [Finsupp.single_apply]
  rw [punctureDivisor, Finset.sum_apply', Finset.sum_congr rfl h,
    Finset.sum_ite_eq' T v (fun _ => (1 : ℤ)), if_pos hv]

theorem punctureDivisor_apply_of_notMem {T : Finset (Place K F)} {v : Place K F}
    (hv : v ∉ T) : punctureDivisor T v = 0 := by
  classical
  have h : ∀ t ∈ T, Finsupp.single t (1 : ℤ) v = (if t = v then (1 : ℤ) else 0) := by
    intro t _
    rw [Finsupp.single_apply]
  rw [punctureDivisor, Finset.sum_apply', Finset.sum_congr rfl h,
    Finset.sum_ite_eq' T v (fun _ => (1 : ℤ)), if_neg hv]

theorem punctureDivisor_sub_single_le (T : Finset (Place K F)) (t : Place K F) :
    punctureDivisor T - Finsupp.single t (1 : ℤ) ≤ punctureDivisor T := by
  classical
  rw [Finsupp.le_def]
  intro v
  rw [Finsupp.sub_apply]
  have hs : (0 : ℤ) ≤ Finsupp.single t (1 : ℤ) v := by
    rw [Finsupp.single_apply]
    split_ifs <;> omega
  linarith

theorem degree_punctureDivisor [IsAlgClosed K] [IsCurveOver K F]
    (T : Finset (Place K F)) :
    Divisor.degree (punctureDivisor T) = (T.card : ℤ) := by
  classical
  rw [punctureDivisor, map_sum]
  have h : ∀ t ∈ T, Divisor.degree (Finsupp.single t (1 : ℤ)) = 1 := by
    intro t _
    rw [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed t]
    norm_num
  rw [Finset.sum_congr rfl h]
  simp

theorem canonical_degree_le_two_genus [HasCanonicalDivisor (K := K) (F := F)]
    (hex : ∃ ω : Ω[F⁄K], ω ≠ 0) :
    Divisor.degree (canonicalDivisorOf hex.choose_spec) ≤ 2 * (genus K F : ℤ) - 1 := by
  generalize hd : Divisor.degree (canonicalDivisorOf hex.choose_spec) = d
  have hgenus : genus K F = ((d + 2).toNat / 2 : ℕ) := by
    rw [genus, dif_pos hex, hd]
  rcases lt_or_ge (d + 2) 0 with hneg | hpos
  · have hzero : (d + 2).toNat = 0 := Int.toNat_of_nonpos (le_of_lt hneg)
    rw [hgenus, hzero]
    omega
  · have hcast : ((d + 2).toNat : ℤ) = d + 2 := Int.toNat_of_nonneg hpos
    have hmod : (2 : ℤ) * (((d + 2).toNat / 2 : ℕ) : ℤ)
        + (((d + 2).toNat % 2 : ℕ) : ℤ) = ((d + 2).toNat : ℤ) := by
      have h := Nat.div_add_mod (d + 2).toNat 2
      exact_mod_cast h
    have hlt : (((d + 2).toNat % 2 : ℕ) : ℤ) < 2 := by
      have h := Nat.mod_lt (d + 2).toNat (by norm_num : 0 < 2)
      exact_mod_cast h
    have hnn : (0 : ℤ) ≤ (((d + 2).toNat % 2 : ℕ) : ℤ) := Int.natCast_nonneg _
    rw [hgenus]
    omega

end PortedAPI

/-! ## PART 3: main theorem — zero divisor = sum_T [t], hRR and hdual DISCHARGED -/

section MainTheorem

open AlgebraicCurve

variable {K F : Type*} [Field K] [IsAlgClosed K] [Infinite K]
  [DecidableEq (RatFunc K)] [Field F] [Algebra K F]
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

theorem zero_divisor_exists_proved
    (T : Finset (Place K F)) (hcard : 2 * genus K F + 1 ≤ T.card) :
    ∃ g : F, g ≠ 0 ∧ (∀ p : Place K F, 0 < p.ord g ↔ p ∈ T) ∧
      ∀ t ∈ T, t.ord g = 1 := by
  classical
  have hRR : FunctionFieldRiemannRoch K F :=
    LeanFormal.IUT.XiFPaper.Mzk1RRProvedActual.functionFieldRiemannRoch_proved
      (K := K) (F := F)
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[F⁄K])
  let hex : ∃ ω : Ω[F⁄K], ω ≠ 0 := ⟨ω, hω⟩
  have hωc : hex.choose ≠ 0 := hex.choose_spec
  have hKbound := canonical_degree_le_two_genus (K := K) (F := F) hex
  have hdegT : Divisor.degree (punctureDivisor T) = (T.card : ℤ) := degree_punctureDivisor T
  have hcardZ : (2 * (genus K F : ℤ) + 1) ≤ (T.card : ℤ) := by exact_mod_cast hcard
  have hTpos : 0 < T.card := by omega
  have hTne : T.Nonempty := Finset.card_pos.mp hTpos
  have hdual : ∀ t ∈ T,
      (ell (canonicalDivisorOf hex.choose_spec - punctureDivisor T) : ℤ) = 0 ∧
      (ell (canonicalDivisorOf hex.choose_spec - (punctureDivisor T - Finsupp.single t (1 : ℤ))) : ℤ) = 0 := by
    intro t ht
    have hlt1 : Divisor.degree (canonicalDivisorOf hex.choose_spec - punctureDivisor T) < 0 := by
      rw [map_sub, hdegT]
      linarith [hKbound, hcardZ]
    have hdegsub : Divisor.degree (punctureDivisor T - Finsupp.single t (1 : ℤ))
        = (T.card : ℤ) - 1 := by
      rw [map_sub, hdegT, Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed t]
      norm_num
    have hlt2 : Divisor.degree
        (canonicalDivisorOf hex.choose_spec - (punctureDivisor T - Finsupp.single t (1 : ℤ))) < 0 := by
      rw [map_sub, hdegsub]
      linarith [hKbound, hcardZ]
    exact ⟨by simpa using (AlgebraicCurve.ell_eq_zero_of_degree_neg hlt1),
      by simpa using (AlgebraicCurve.ell_eq_zero_of_degree_neg hlt2)⟩
  have hproper : ∀ t ∈ T,
      LSpace (punctureDivisor T - Finsupp.single t (1 : ℤ)) < LSpace (punctureDivisor T) := by
    intro t ht
    refine lt_of_le_of_ne (lSpace_mono (punctureDivisor_sub_single_le T t)) ?_
    intro heq
    have h1 : (ell (punctureDivisor T) : ℤ)
        - (ell (canonicalDivisorOf hex.choose_spec - punctureDivisor T) : ℤ)
        = (Divisor.degree (punctureDivisor T) : ℤ) + 1 - (genus K F : ℤ) := by
      have h := hRR hex.choose_spec (punctureDivisor T)
      exact_mod_cast h
    have h2 : (ell (punctureDivisor T - Finsupp.single t (1 : ℤ)) : ℤ)
        - (ell (canonicalDivisorOf hex.choose_spec
            - (punctureDivisor T - Finsupp.single t (1 : ℤ))) : ℤ)
        = ((Divisor.degree (punctureDivisor T) : ℤ) - 1) + 1 - (genus K F : ℤ) := by
      have h := hRR hex.choose_spec (punctureDivisor T - Finsupp.single t (1 : ℤ))
      have hdeg : (Divisor.degree (punctureDivisor T - Finsupp.single t (1 : ℤ)) : ℤ)
          = (Divisor.degree (punctureDivisor T) : ℤ) - 1 := by
        rw [map_sub, Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed t]
        norm_num
      rw [hdeg] at h
      exact_mod_cast h
    have hdrop := ell_drop_of_rr h1 h2 (hdual t ht).1 (hdual t ht).2
    have heq' : (ell (punctureDivisor T - Finsupp.single t (1 : ℤ)) : ℤ)
        = (ell (punctureDivisor T) : ℤ) :=
      congrArg (fun s : Submodule K F => (Module.finrank K s : ℤ)) heq
    linarith
  let X : PencilData K F (Place K F) :=
    { ord := fun (p : Place K F) (f : F) => p.ord f
      T := T
      LD := LSpace (punctureDivisor T)
      LDt := fun t => LSpace (punctureDivisor T - Finsupp.single t (1 : ℤ))
      proper := hproper
      pole := by
        intro h hh t ht hmem
        have hnot : ¬ (h = 0 ∨ ∀ v : Place K F,
            -(punctureDivisor T - Finsupp.single t (1 : ℤ)) v ≤ v.ord h) := by
          simpa only [mem_lSpace_iff_ord] using hmem
        obtain ⟨hh0, hnotall⟩ := not_or.mp hnot
        obtain ⟨v, hv⟩ := not_forall.mp hnotall
        rw [not_le] at hv
        have hreg : ∀ w : Place K F, -punctureDivisor T w ≤ w.ord h :=
          (mem_lSpace_iff_ord.mp hh).resolve_left hh0
        by_cases hvt : v = t
        · rw [hvt] at hv
          have hDt : punctureDivisor T t = 1 := punctureDivisor_apply_of_mem ht
          have hval : (punctureDivisor T - Finsupp.single t (1 : ℤ)) t = 0 := by
            rw [Finsupp.sub_apply, hDt, Finsupp.single_eq_same]
            norm_num
          rw [hval, neg_zero] at hv
          have hge : -1 ≤ t.ord h := by
            have := hreg t
            rwa [hDt] at this
          omega
        · exfalso
          have hsingle : Finsupp.single t (1 : ℤ) v = 0 := by
            rw [Finsupp.single_apply, if_neg (Ne.symm hvt)]
          have hval : (punctureDivisor T - Finsupp.single t (1 : ℤ)) v
              = punctureDivisor T v := by
            rw [Finsupp.sub_apply, hsingle, sub_zero]
          rw [hval] at hv
          exact absurd hv (not_lt.mpr (hreg v))
      regular := by
        intro h hh hh0 p hp
        have hreg := (mem_lSpace_iff_ord.mp hh).resolve_left hh0
        have hDp : punctureDivisor T p = 0 := punctureDivisor_apply_of_notMem hp
        simpa [hDp] using hreg p
      ord_inv := by
        intro p f _
        exact Place.ord_inv p f }
  obtain ⟨g, hg0, hzero, hno⟩ := exists_function_with_zero_divisor X hTne
  refine ⟨g, hg0, ?_, hzero⟩
  intro p
  constructor
  · intro hp
    by_contra hpT
    exact absurd hp (not_lt.mpr (hno p hpT))
  · intro hp
    show 0 < X.ord p g
    rw [hzero p hp]
    norm_num

end MainTheorem

/-! ## PART 4: rows -/

def rrProvedRows : List (String × String × String) :=
  [ ("Riemann-Roch functionFieldRiemannRoch_proved", "DISCHARGED (PROVED)", "Mzk1RRProvedActual re-export of flt_core real port; axioms trio")
  , ("hdual (dual vanishing)", "DISCHARGED (PROVED)", "flt_core ell_eq_zero_of_degree_neg + canonical_degree_le_two_genus + deg puncture = |T|")
  , ("canonical degree bound deg K <= 2g-1", "PROVED canonical_degree_le_two_genus", "from the rounded genus definition (equality 2g-2 not needed here)")
  , ("puncture divisor deg = |T|", "PROVED degree_punctureDivisor", "IsCurveOver.deg_eq_one_of_isAlgClosed")
  , ("pencil construction (proper subspaces, g = h^{-1})", "PROVED", "ell_drop_of_rr + exists_mem_notMem_of_proper + PencilData; flt_core API")
  , ("zero divisor exactly sum_T [t]", "PROVED zero_divisor_exists_proved", "RR + hdual both discharged; named inputs NONE in this file")
  , ("legacy flt_test root foundation", "LEGACY", "tmp/sheaf/xif/paper/Mzk1GeomCoreFoundationActual.lean (base PROVED; zero_divisor_exists RR-conditional) — cannot be imported together with flt_core")
  , ("scheme <-> function-field bridge", "NOT-YET (legacy root)", "no API linking fm.f to F; scheme layer stays in the flt_test-root legacy file")
  , ("finite map to P^1", "NAMED INPUT (legacy root)", "Mzk1FiniteMapData existence; construction not in this function-field file") ]

theorem rrProvedRows_length : rrProvedRows.length = 9 := rfl

#check zero_divisor_exists_proved
#check degree_punctureDivisor
#check canonical_degree_le_two_genus
#check rrProvedRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeomCoreRRProvedActual
end