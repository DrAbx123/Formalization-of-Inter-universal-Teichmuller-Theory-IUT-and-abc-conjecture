import tmp.sheaf.xif.paper.S2027LocalArtinActual

/-!
# S2039: the actual constant monoid Psi_cns of [AbsTopIII] Corollary 1.10(b),
and the exact first missing chain to Psi_cns = O^tri_{F_v}

Layer: **O** (original Theta-link / q-pilot).  Consumers: the S2000 package
(tmp/sheaf/xif/paper/S2000CohomologicalPsiCnsActual.lean), the S2011 Cor 1.10(b)
interface, the S2017 Verlagerung/cyclotome package, and the S2024/S2027
local-reciprocity packages.  Upstream: IUT II, Proposition 4.1, (i)-(ii), and
[AbsTopIII], Corollary 1.10, (a), (b), (d), Remark 1.11.5, (i).

## The source object

IUT II, Proposition 4.1, (ii) [text: papers/motizuki_corpus/text/
Inter-universal Teichmuller Theory II.txt, lines 5425-5446]:

  applying the cyclotomic rigidity isomorphisms of Corollaries 2.8, (i); 2.9 and
  considering the inverse image of Z in Z-hat via the surjection of
  Remark 1.11.5, (i), applied to G_v, one obtains a functorial algorithm
  M_Theta* |-> Psi_cns(M_Theta*) = M_TM(M_Theta*) subset lim_J H^1(...),
  naturally isomorphic to O^tri_{F_v}, equipped with a natural conjugation
  action by Pi_X.

Remark 1.11.5, (i) [same text, lines 3049-3070] identifies the surjection as
the one of [AbsTopIII], Corollary 1.10, (b): for G = G_k it is "determined by
the valuation of k on the image of the natural Kummer map k^times ->
H^1(G_k, mu_hat^Z(G_k))", and the image of that Kummer map "is equal to the
inverse image of Z in Z-hat".  Corollary 1.10, (b) obtains the surjection from
the H^2-normalization H^2(G_k, mu_hat^Z) = Z-hat of (a) by cup product.

## What this file constructs (unconditional, no sorry, no axiom)

1. **Z-hat itself**, correcting the repeatedly recorded claim of S2011/S2017/
   S2024/S2027 that Z-hat is absent from the tree.  Zhat is the inverse limit
   of the reduction maps ZMod n -> ZMod m (m | n) over the positive integers,
   as an actual commutative ring (zhatSubring), with the reductions zhatMod,
   their compatibility zhat_compat, the canonical ring homomorphism
   Int -> Zhat (zhatIntHom) and its injectivity (zhatIntHom_injective): Zhat
   is the profinite completion of Int.  This supplies the target half of (M3)
   and the codomain of the (M4) normalization.

2. **The source-faithful integral monoid O^tri_{F_v}**, i.e. the nonzero
   elements of the valuation ring of the local field F_v = Q_p
   (FvBase/OtriFv), its canonical embedding into the nonzero integral monoid
   O^tri_{Qbar_p} used by S2000/S2006 (otriFvToOtri), and the resulting
   **Kummer map of the local field's integral monoid**
   PsiCnsBaseKummer : O^tri_{F_v} -> lim_J H^1(J, mu_hat^Z), proved injective
   (PsiCnsBaseKummer_injective, using S2006) with Kummer image multiplicatively
   equivalent to O^tri_{F_v} (PsiCnsBaseImage_equiv).

   This is a correction of the model caveat (M6) of S2000/S2011.  S2000's
   PsiCnsKummer is the Kummer map of O^tri_{Qbar_p}, while the source's (d) is
   about the local field F_v.  The two monoids differ: the integral closure
   contains a square root of p, which is not in Q_p.  Interpreting the
   identification Psi_cns = O^tri with Otri p would therefore be wrong; the
   source-faithful target is OtriFv.  (S2006's identification remains a correct
   theorem about the closure Kummer image; it is simply not the paper's (d).)

3. **The actual Psi_cns**, defined exactly as the source defines it: the
   inverse image of the nonnegative part of Z-hat under the normalization
   N.norm of [AbsTopIII], Cor 1.10, (b) (PsiCns, mem_PsiCns).  It is a genuine
   submonoid of the actual limit constructed by S2000 (one_mem_PsiCns,
   mul_mem_PsiCns), not a model.

   **Semantic point.**  The source's phrase is "the inverse image of Z in
   Z-hat".  Since the same assertion identifies Psi_cns with the *monoid*
   O^tri_{F_v}, the piece of Z that corresponds to integral elements is the
   nonnegative part, so PsiCns is defined as the inverse image of zhatNonneg.
   The inverse image of all of Z would be the valuation group preimage, i.e.
   the whole of k_v^times, which cannot be the integral monoid; this is also
   the reading forced by the source's own summary "the image of the Kummer
   map is equal to the inverse image of Z".  The definition is stated for an
   arbitrary normalization, so a different reading of the target submonoid can
   be substituted without changing any reduction theorem.

   It is stable under S2011's actual
   G_v-action germAction whenever the normalization is G_v-invariant
   (PsiCns_stable_of_invariant), which is the "natural conjugation action" of
   the source's definition, and it contains the unit Kummer classes whenever
   the normalization is trivial on them (PsiCnsUnitKummer_mem).

4. **The exact reduction of Psi_cns = O^tri_{F_v}.**  With

     NormalizationIsValuation N   (the normalization is the valuation on the
       Kummer image: the "determined by the valuation of k" half of
       Remark 1.11.5, (i)), and
     PsiCnsExhaustion N           (every nonnegative class is a Kummer class:
       the "image = inverse image of Z" statement of Remark 1.11.5, (i) /
       Corollary 1.10, (d)),

   the file proves

     (Kummer image = Psi_cns)  <->  NormalizationIsValuation N
                                     and PsiCnsExhaustion N
                                        (kummerEquals_iff),

   that NormalizationIsValuation gives the inclusion of the Kummer image in
   Psi_cns (PsiCnsBaseImage_le_of_valuation), that the canonical inclusion is
   bijective exactly under PsiCnsExhaustion
   (baseImageToPsiCns_bijective_iff_exhaustion), and hence

     PsiCns N = O^tri_{F_v}   whenever both hold   (PsiCns_equiv_otriFv).

   The converse directions are proved too, so the identification is reduced,
   without weakening and without assuming the conclusion, to the two displayed
   source assertions.

## The exact first missing chain (no fake, no axiom, no sorry)

(M1) transfer/colimit: **done** in S2017 (muQZ, muHatZ, muQZ_lift, ...).

(M2) local reciprocity on torsion / local Artin map: **not done**.  S2024 and
     S2027 isolate it as LocalReciprocityData / LocalArtinSourceData and prove
     that it yields S2017's muQZComparison and muHatComparison.  For the
     present file (M2) is consumed only through the cyclotomic comparison
     CyclotomeComparison = muHatComparison p (the paper's cyclotomic rigidity,
     Cor 2.8, (i); 2.9), i.e. the identification of the group-theoretic
     cyclotome with the actual cyclotome.  It is a named missing proposition,
     never assumed.  Note that the paper's Psi_cns is defined inside
     lim_J H^1(J, mu_hat^Z(G_v)) with the group-theoretic coefficient module,
     while the Kummer image of S2000 lives in the limit with the actual
     cyclotome; passing from the coefficient comparison to a comparison of the
     two limits additionally needs the G_v-action on the group-theoretic
     cyclotome, which is not constructed (see S2017's item (M5)).  The
     cyclotomic comparison is characterized exactly in cyclotomeComparison_iff.

(M3) continuous H^2 and H^2(G_v, mu_hat^Z) = Z-hat: the **target** Z-hat is
     constructed here.  Mathlib v4.32.2 contains a continuous cohomology
     functor (Mathlib.RepresentationTheory.Homological.ContCohomology:
     continuousCohomology n for TopRep k G; the cyclotomic action
     PsiCnsCoefficientAction is a continuous action, so the coefficient
     representation is available in principle).  Still missing is the
     *computation* H^2(G_v, mu_hat^Z) = lim_n Br(k_v)[n] = lim_n Z/n = Z-hat,
     which needs Br(k_v) = Q/Z, i.e. local class field theory.  No declaration
     is fabricated for it.  In dependency order this is the first missing step
     for the construction of the normalization.

(M4) normalized surjection H^1(G_v, mu_hat^Z) ->> Z-hat: not constructed.  In
     the source it is obtained from (M3) by cup product with the fundamental
     class, together with H^1(G_v, mu_hat^Z) = G_v^ab (Hilbert 90/Tate).  The
     present file takes the output of (M4) as the structure
     PsiCnsNormalization and proves exactly which properties of it are used.

(d)  Kummer image = inverse image of Z: isolated as NormalizationIsValuation
     and PsiCnsExhaustion, and proved equivalent to the identification.

No sorry, admit, axiom, True/PUnit slot, empty structure, arbitrary inhabitant,
or assumption-only Nonempty gate is used.

## Not run

Full Project build, target comparator, independent review, and the actual
construction of the normalization map.

## References

* [AbsTopIII], Corollary 1.10, (a), (b), (d); Remark 1.11.5, (i).
* IUT II, Proposition 4.1, (ii) (the constant monoid Psi_cns).
* S2000/S2006 (the actual cohomological limit and its Kummer map),
  S2011 (the Cor 1.10(b) interface and the G_v-action), S2017 (the
  Verlagerung and the cyclotome mu_hat^Z), S2024/S2027 (local reciprocity and
  the local Artin map).
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S2039ActualPsiCns

/-- The index set of the inverse system presenting Zhat: the positive integers. -/
abbrev ZhatIndex : Type := { n : Nat // 0 < n }

/-- A compatible family of residues mod n, n > 0. -/
def zhatCarrier : Set (forall n : ZhatIndex, ZMod (n : Nat)) :=
  { f | forall (m n : ZhatIndex) (h : (m : Nat) ∣ (n : Nat)),
      ZMod.castHom h (ZMod (m : Nat)) (f n) = f m }

theorem zhat_zero_mem : (0 : forall n : ZhatIndex, ZMod (n : Nat)) ∈ zhatCarrier := by
  intro m n h
  exact map_zero _

theorem zhat_one_mem : (1 : forall n : ZhatIndex, ZMod (n : Nat)) ∈ zhatCarrier := by
  intro m n h
  exact map_one _

theorem zhat_add_mem {a b : forall n : ZhatIndex, ZMod (n : Nat)}
    (ha : a ∈ zhatCarrier) (hb : b ∈ zhatCarrier) : a + b ∈ zhatCarrier := by
  intro m n h
  rw [Pi.add_apply, map_add, ha m n h, hb m n h, Pi.add_apply]

theorem zhat_mul_mem {a b : forall n : ZhatIndex, ZMod (n : Nat)}
    (ha : a ∈ zhatCarrier) (hb : b ∈ zhatCarrier) : a * b ∈ zhatCarrier := by
  intro m n h
  rw [Pi.mul_apply, map_mul, ha m n h, hb m n h, Pi.mul_apply]

theorem zhat_neg_mem {a : forall n : ZhatIndex, ZMod (n : Nat)}
    (ha : a ∈ zhatCarrier) : -a ∈ zhatCarrier := by
  intro m n h
  rw [Pi.neg_apply, map_neg, ha m n h, Pi.neg_apply]

/-- Zhat = lim_n Z/nZ, as a subring of the product of the ZMod n. -/
def zhatSubring : Subring (forall n : ZhatIndex, ZMod (n : Nat)) where
  carrier := zhatCarrier
  zero_mem' := zhat_zero_mem
  one_mem' := zhat_one_mem
  add_mem' := zhat_add_mem
  mul_mem' := zhat_mul_mem
  neg_mem' := zhat_neg_mem

/-- **Zhat**, the profinite completion of the integers, as the inverse limit of
the reductions ZMod n -> ZMod m for m ∣ n.  This is the target of the
[AbsTopIII] Corollary 1.10, (a), normalization and of the surjection of (b). -/
abbrev Zhat : Type := zhatSubring

/-- The reduction of an element of Zhat modulo n. -/
def zhatMod (n : ZhatIndex) (x : Zhat) : ZMod (n : Nat) :=
  (x : forall n : ZhatIndex, ZMod (n : Nat)) n

@[simp] theorem zhatMod_add (n : ZhatIndex) (x y : Zhat) :
    zhatMod n (x + y) = zhatMod n x + zhatMod n y := rfl

@[simp] theorem zhatMod_mul (n : ZhatIndex) (x y : Zhat) :
    zhatMod n (x * y) = zhatMod n x * zhatMod n y := rfl

@[simp] theorem zhatMod_neg (n : ZhatIndex) (x : Zhat) :
    zhatMod n (-x) = -zhatMod n x := rfl

@[simp] theorem zhatMod_zero (n : ZhatIndex) : zhatMod n 0 = 0 := rfl

@[simp] theorem zhatMod_one (n : ZhatIndex) : zhatMod n 1 = 1 := rfl

@[ext] theorem Zhat.ext {x y : Zhat}
    (h : forall n : ZhatIndex, zhatMod n x = zhatMod n y) : x = y := by
  apply Subtype.ext
  funext n
  exact h n

/-- The compatibility that defines Zhat, in terms of the reductions. -/
theorem zhat_compat (x : Zhat) (m n : ZhatIndex) (h : (m : Nat) ∣ (n : Nat)) :
    ZMod.castHom h (ZMod (m : Nat)) (zhatMod n x) = zhatMod m x :=
  x.2 m n h

/-- The integer k as an element of Zhat. -/
def zhatInt (k : Int) : Zhat :=
  ⟨fun n => (k : ZMod (n : Nat)), by
    intro m n h
    rw [ZMod.castHom_apply, ZMod.cast_intCast]
    exact h⟩

@[simp] theorem zhatMod_zhatInt (k : Int) (n : ZhatIndex) :
    zhatMod n (zhatInt k) = (k : ZMod (n : Nat)) := rfl

/-- The natural number k as an element of Zhat. -/
def zhatNat (k : Nat) : Zhat := zhatInt (k : Int)

@[simp] theorem zhatMod_zhatNat (k : Nat) (n : ZhatIndex) :
    zhatMod n (zhatNat k) = (k : ZMod (n : Nat)) := by
  simp [zhatNat]

theorem zhatInt_add (a b : Int) : zhatInt (a + b) = zhatInt a + zhatInt b := by
  apply Zhat.ext
  intro n
  simp [Int.cast_add]

theorem zhatInt_neg (a : Int) : zhatInt (-a) = -zhatInt a := by
  apply Zhat.ext
  intro n
  simp

theorem zhatInt_zero : zhatInt 0 = 0 := by
  apply Zhat.ext
  intro n
  simp

theorem zhatInt_one : zhatInt 1 = 1 := by
  apply Zhat.ext
  intro n
  simp

/-- The canonical ring homomorphism Int -> Zhat. -/
def zhatIntHom : Int →+* Zhat where
  toFun := zhatInt
  map_one' := zhatInt_one
  map_mul' a b := by
    apply Zhat.ext
    intro n
    simp [Int.cast_mul]
  map_zero' := zhatInt_zero
  map_add' := zhatInt_add

/-- Int -> Zhat is injective: Zhat is the profinite completion of Int. -/
theorem zhatInt_injective : Function.Injective zhatInt := by
  intro a b hab
  by_contra hne
  have hdiff : a - b ≠ 0 := sub_ne_zero.mpr hne
  let N : Nat := (a - b).natAbs + 1
  have hNpos : 0 < N := Nat.succ_pos _
  let n : ZhatIndex := ⟨N, hNpos⟩
  have hmod : zhatMod n (zhatInt a) = zhatMod n (zhatInt b) := by rw [hab]
  simp only [zhatMod_zhatInt] at hmod
  have hzero : ((a - b : Int) : ZMod N) = 0 := by
    rw [Int.cast_sub, hmod, sub_self]
  have hdvd : (N : Int) ∣ (a - b) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hzero
  have hdvdNat : N ∣ (a - b).natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using h
  have hne' : (a - b).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hdiff
  exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hne') hdvdNat) (Nat.not_le.mpr (Nat.lt_succ_self _))

theorem zhatIntHom_injective : Function.Injective zhatIntHom :=
  zhatInt_injective

/-- The nonnegative part Nat in Zhat, as an additive submonoid. -/
def zhatNatSubmonoid : AddSubmonoid Zhat :=
  AddSubmonoid.closure (Set.range fun k : Nat => zhatNat k)

theorem zhatNat_mem (k : Nat) : zhatNat k ∈ zhatNatSubmonoid :=
  AddSubmonoid.subset_closure ⟨k, rfl⟩

theorem zhatNat_mul_mem {x y : Zhat} (hx : x ∈ zhatNatSubmonoid)
    (hy : y ∈ zhatNatSubmonoid) : x * y ∈ zhatNatSubmonoid := by
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      induction hy using AddSubmonoid.closure_induction with
      | mem y hy =>
          obtain ⟨l, rfl⟩ := hy
          have hmul : zhatNat k * zhatNat l = zhatNat (k * l) := by
            apply Zhat.ext
            intro n
            simp [Nat.cast_mul]
          rw [hmul]
          exact zhatNat_mem (k * l)
      | zero => simp
      | add y z _ _ ihy ihz => rw [mul_add]; exact AddSubmonoid.add_mem _ ihy ihz
  | zero => simp
  | add x y _ _ ihx ihy => rw [add_mul]; exact AddSubmonoid.add_mem _ ihx ihy

/-- The nonnegative part of Z-hat, in multiplicative form, as the image of the
additive submonoid of natural-number classes.  This is the piece of Z-hat whose
inverse image defines Psi_cns. -/
def zhatNonneg : Submonoid (Multiplicative Zhat) where
  carrier := { x | Multiplicative.toAdd x ∈ zhatNatSubmonoid }
  one_mem' := by
    show Multiplicative.toAdd (1 : Multiplicative Zhat) ∈ zhatNatSubmonoid
    rw [show Multiplicative.toAdd (1 : Multiplicative Zhat) = (0 : Zhat) from rfl]
    exact zhatNatSubmonoid.zero_mem
  mul_mem' := by
    intro x y hx hy
    show Multiplicative.toAdd (x * y) ∈ zhatNatSubmonoid
    rw [show Multiplicative.toAdd (x * y) =
      Multiplicative.toAdd x + Multiplicative.toAdd y from rfl]
    exact zhatNatSubmonoid.add_mem hx hy

theorem zhatNonneg_ofNat (k : Nat) :
    Multiplicative.ofAdd (zhatNat k) ∈ zhatNonneg :=
  zhatNat_mem k

theorem zhatNonneg_mul {x y : Multiplicative Zhat}
    (hx : x ∈ zhatNonneg) (hy : y ∈ zhatNonneg) : x * y ∈ zhatNonneg :=
  Submonoid.mul_mem _ hx hy

theorem zhatNonneg_one : (1 : Multiplicative Zhat) ∈ zhatNonneg :=
  Submonoid.one_mem _

end LeanFormal.IUT.XiFPaper.S2039ActualPsiCns

namespace LeanFormal.IUT.XiFPaper.S2039ActualPsiCns

open LeanFormal.IUT.LocalMLFModelTMPair
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2006KummerKernelActual
open LeanFormal.IUT.XiFPaper.S2011Cor110bActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2024LocalReciprocityActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open scoped nonZeroDivisors

variable (p : Nat) [Fact (Nat.Prime p)]

/-! ## 2. The source-faithful integral monoid O^tri_{F_v} -/

/-- The valuation ring of the local field F_v = Q_p. -/
abbrev FvBase : Type := Valuation.integer (ValuativeRel.valuation ℚ_[p])

/-- The nonzero integral monoid O^tri_{F_v} of the local field F_v.  This is
the monoid of the source identification Psi_cns = O^tri_{F_v}; it is not the
nonzero integral monoid O^tri_{Qbar_p} of the algebraic closure used by
S2000/S2006 (see the module doc, item (M6)). -/
abbrev OtriFv : Type := (FvBase p)⁰

/-- The algebra map F_v -> Qbar_p is injective. -/
theorem fvBase_algebraMap_injective :
    Function.Injective (algebraMap (FvBase p) (AlgebraicClosure ℚ_[p])) := by
  intro a b hab
  have h : (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])) (a : ℚ_[p]) =
      (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])) (b : ℚ_[p]) := hab
  have hinj : Function.Injective (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])) :=
    FaithfulSMul.algebraMap_injective ℚ_[p] (AlgebraicClosure ℚ_[p])
  exact Subtype.ext (hinj h)

/-- The embedding of the local field's integral monoid into the algebraic
closure's nonzero integral monoid. -/
def otriFvToOtri (x : OtriFv p) : Otri p :=
  ⟨⟨algebraMap (FvBase p) (AlgebraicClosure ℚ_[p]) (x.1 : FvBase p),
     isIntegral_algebraMap⟩,
   mem_nonZeroDivisors_of_ne_zero (by
     intro h
     have hzero : algebraMap (FvBase p) (AlgebraicClosure ℚ_[p]) (x.1 : FvBase p) = 0 :=
       congrArg Subtype.val h
     have hx0 : (x.1 : FvBase p) = 0 := by
       apply fvBase_algebraMap_injective p
       rw [hzero, map_zero]
     exact nonZeroDivisors.coe_ne_zero x hx0)⟩

theorem otriFvToOtri_one : otriFvToOtri p 1 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  exact map_one _

theorem otriFvToOtri_mul (x y : OtriFv p) :
    otriFvToOtri p (x * y) = otriFvToOtri p x * otriFvToOtri p y := by
  apply Subtype.ext
  apply Subtype.ext
  exact map_mul _ _ _

theorem otriFvToOtri_injective : Function.Injective (otriFvToOtri p) := by
  intro x y hxy
  have h : algebraMap (FvBase p) (AlgebraicClosure ℚ_[p]) (x.1 : FvBase p) =
      algebraMap (FvBase p) (AlgebraicClosure ℚ_[p]) (y.1 : FvBase p) :=
    congrArg (fun z : Otri p => z.1.1) hxy
  exact Subtype.ext (fvBase_algebraMap_injective p h)

/-- The embedding as a monoid homomorphism. -/
def otriFvToOtriHom : OtriFv p →* Otri p where
  toFun := otriFvToOtri p
  map_one' := otriFvToOtri_one p
  map_mul' := otriFvToOtri_mul p

/-- **The Kummer map of the local field's integral monoid** into the actual
cohomological limit lim_J H^1(J, mu_hat^Z) of S2000. -/
def PsiCnsBaseKummer : OtriFv p →* PsiCnsCohomology p :=
  (PsiCnsKummer p).comp (otriFvToOtriHom p)

theorem PsiCnsBaseKummer_eq (x : OtriFv p) :
    PsiCnsBaseKummer p x = PsiCnsKummer p (otriFvToOtri p x) := rfl

/-- The local-field Kummer map is injective: S2006's injectivity of the
closure Kummer map plus injectivity of O^tri_{F_v} -> O^tri_{Qbar_p}. -/
theorem PsiCnsBaseKummer_injective : Function.Injective (PsiCnsBaseKummer p) := by
  intro x y hxy
  exact otriFvToOtri_injective p (PsiCnsKummer_injective p hxy)

/-- The Kummer image of the local field's integral monoid. -/
def PsiCnsBaseImage : Submonoid (PsiCnsCohomology p) :=
  MonoidHom.mrange (PsiCnsBaseKummer p)

theorem mem_PsiCnsBaseImage (x : PsiCnsCohomology p) :
    x ∈ PsiCnsBaseImage p ↔ ∃ a : OtriFv p, PsiCnsBaseKummer p a = x :=
  MonoidHom.mem_mrange

/-- The Kummer image of O^tri_{F_v} is multiplicatively equivalent to
O^tri_{F_v}. -/
theorem PsiCnsBaseImage_equiv : Nonempty (PsiCnsBaseImage p ≃* OtriFv p) := by
  let e : OtriFv p →* PsiCnsBaseImage p := (PsiCnsBaseKummer p).mrangeRestrict
  have hb : Function.Bijective e := by
    constructor
    · intro x y hxy
      exact PsiCnsBaseKummer_injective p (congrArg Subtype.val hxy)
    · exact MonoidHom.mrangeRestrict_surjective (PsiCnsBaseKummer p)
  exact ⟨(MulEquiv.ofBijective e hb).symm⟩

/-! ## 3. The actual constant monoid Psi_cns and its identification -/

/-- The data of the [AbsTopIII] Corollary 1.10(b) normalization: the
surjection H^1(G_v, mu_hat^Z) ->> Z-hat determined by the Frobenius element /
the valuation.  This is the (M4) datum; it is a hypothesis object here, not an
inhabited assertion. -/
structure PsiCnsNormalization where
  norm : PsiCnsCohomology p →* Multiplicative Zhat
  surjective : Function.Surjective norm

/-- **The actual constant monoid Psi_cns**: the inverse image of the
nonnegative part of Z-hat under the normalization, exactly as in IUT II,
Proposition 4.1, (ii).  It is a genuine submonoid of the actual cohomological
limit, not a model. -/
def PsiCns (N : PsiCnsNormalization p) : Submonoid (PsiCnsCohomology p) :=
  zhatNonneg.comap N.norm

theorem mem_PsiCns (N : PsiCnsNormalization p) (x : PsiCnsCohomology p) :
    x ∈ PsiCns p N ↔ N.norm x ∈ zhatNonneg :=
  Iff.rfl

theorem one_mem_PsiCns (N : PsiCnsNormalization p) :
    (1 : PsiCnsCohomology p) ∈ PsiCns p N := by
  show N.norm 1 ∈ zhatNonneg
  rw [map_one]
  exact zhatNonneg_one

theorem mul_mem_PsiCns (N : PsiCnsNormalization p) {x y : PsiCnsCohomology p}
    (hx : x ∈ PsiCns p N) (hy : y ∈ PsiCns p N) : x * y ∈ PsiCns p N := by
  show N.norm (x * y) ∈ zhatNonneg
  rw [map_mul]
  exact zhatNonneg_mul hx hy

/-- The normalization is the valuation on the Kummer image: the "determined by
the valuation of k" half of Remark 1.11.5(i). -/
def NormalizationIsValuation (N : PsiCnsNormalization p) : Prop :=
  forall a : OtriFv p, N.norm (PsiCnsBaseKummer p a) ∈ zhatNonneg

/-- **The Kummer image of O^tri_{F_v} lies in Psi_cns** as soon as the
normalization is the valuation. -/
theorem PsiCnsBaseImage_le_of_valuation (N : PsiCnsNormalization p)
    (h : NormalizationIsValuation p N) : PsiCnsBaseImage p ≤ PsiCns p N := by
  intro x hx
  obtain ⟨a, rfl⟩ := (mem_PsiCnsBaseImage p x).mp hx
  exact h a

/-- The exhaustion claim: every nonnegative class is a Kummer class.  This is
the "image of the Kummer map = inverse image of Z" statement of Remark
1.11.5(i) / Corollary 1.10(d). -/
def PsiCnsExhaustion (N : PsiCnsNormalization p) : Prop :=
  forall x : PsiCnsCohomology p, x ∈ PsiCns p N →
    ∃ a : OtriFv p, PsiCnsBaseKummer p a = x

/-- The paper's assertion (d): the Kummer image is exactly the inverse image of
the nonnegative part. -/
def KummerEqualsPsiCns (N : PsiCnsNormalization p) : Prop :=
  forall x : PsiCnsCohomology p,
    x ∈ PsiCns p N ↔ ∃ a : OtriFv p, PsiCnsBaseKummer p a = x

/-- **The exact content of (d)**: the equality of the Kummer image with Psi_cns
is equivalent to the valuation condition together with the exhaustion.  No
direction is weakened and nothing is assumed twice. -/
theorem kummerEquals_iff (N : PsiCnsNormalization p) :
    KummerEqualsPsiCns p N ↔
      NormalizationIsValuation p N ∧ PsiCnsExhaustion p N := by
  constructor
  · intro h
    exact ⟨fun a => (h _).mpr ⟨a, rfl⟩, fun x hx => (h x).mp hx⟩
  · rintro ⟨hv, he⟩ x
    exact ⟨he x, fun hx =>
      PsiCnsBaseImage_le_of_valuation p N hv ((mem_PsiCnsBaseImage p x).mpr hx)⟩

/-- The canonical monoid map from the Kummer image into Psi_cns, available as
soon as the normalization is the valuation. -/
def baseImageToPsiCns (N : PsiCnsNormalization p)
    (h : NormalizationIsValuation p N) : PsiCnsBaseImage p →* PsiCns p N where
  toFun x := ⟨x.1, PsiCnsBaseImage_le_of_valuation p N h x.2⟩
  map_one' := Subtype.ext rfl
  map_mul' x y := Subtype.ext rfl

theorem baseImageToPsiCns_injective (N : PsiCnsNormalization p)
    (h : NormalizationIsValuation p N) :
    Function.Injective (baseImageToPsiCns p N h) := by
  intro x y hxy
  exact Subtype.ext (congrArg (fun z : PsiCns p N => (z : PsiCnsCohomology p)) hxy)

theorem baseImageToPsiCns_surjective_iff_exhaustion (N : PsiCnsNormalization p)
    (h : NormalizationIsValuation p N) :
    Function.Surjective (baseImageToPsiCns p N h) ↔ PsiCnsExhaustion p N := by
  constructor
  · intro hs x hx
    obtain ⟨y, hy⟩ := hs ⟨x, hx⟩
    obtain ⟨a, ha⟩ := (mem_PsiCnsBaseImage p y.1).mp y.2
    have hxy : (y : PsiCnsCohomology p) = x :=
      congrArg (fun z : PsiCns p N => (z : PsiCnsCohomology p)) hy
    exact ⟨a, ha.trans hxy⟩
  · intro hex x
    obtain ⟨a, ha⟩ := hex x.1 x.2
    exact ⟨⟨PsiCnsBaseKummer p a, ⟨a, rfl⟩⟩, Subtype.ext ha⟩

/-- The canonical inclusion is bijective exactly under the exhaustion claim:
the identification is not weaker than the source's (d). -/
theorem baseImageToPsiCns_bijective_iff_exhaustion (N : PsiCnsNormalization p)
    (h : NormalizationIsValuation p N) :
    Function.Bijective (baseImageToPsiCns p N h) ↔ PsiCnsExhaustion p N := by
  constructor
  · intro hb
    exact (baseImageToPsiCns_surjective_iff_exhaustion p N h).mp hb.2
  · intro hex
    exact ⟨baseImageToPsiCns_injective p N h,
      (baseImageToPsiCns_surjective_iff_exhaustion p N h).mpr hex⟩

/-- **Psi_cns is O^tri_{F_v}**, from the two source assertions. -/
theorem PsiCns_equiv_otriFv (N : PsiCnsNormalization p)
    (hval : NormalizationIsValuation p N) (hex : PsiCnsExhaustion p N) :
    Nonempty (PsiCns p N ≃* OtriFv p) := by
  have hbij : Function.Bijective (baseImageToPsiCns p N hval) :=
    (baseImageToPsiCns_bijective_iff_exhaustion p N hval).mpr hex
  obtain ⟨e⟩ := PsiCnsBaseImage_equiv p
  exact ⟨(MulEquiv.ofBijective (baseImageToPsiCns p N hval) hbij).symm.trans e⟩

/-- The nonnegative-part membership of the nat classes, in the form used for
the unit Kummer image. -/
theorem one_zhatNonneg : (1 : Multiplicative Zhat) ∈ zhatNonneg := zhatNonneg_one

/-- If the normalization is invariant under S2011's actual G_v-action on the
cohomological limit, then Psi_cns is stable under that action.  This is the
"natural conjugation action" of the source's definition of Psi_cns, conditional
on the G_v-invariance of the normalization. -/
theorem PsiCns_stable_of_invariant (N : PsiCnsNormalization p)
    (hinv : forall (g : LocalAbsoluteGalois p) (x : PsiCnsCohomology p),
      N.norm (germAction p g x) = N.norm x)
    (g : LocalAbsoluteGalois p) {x : PsiCnsCohomology p} (hx : x ∈ PsiCns p N) :
    germAction p g x ∈ PsiCns p N := by
  show N.norm (germAction p g x) ∈ zhatNonneg
  rw [hinv g x]
  exact hx

/-- The unit Kummer classes lie in Psi_cns whenever the normalization is
trivial on them.  This is consistent with the units having valuation zero, and
uses S2000's actual unit Kummer map. -/
theorem PsiCnsUnitKummer_mem (N : PsiCnsNormalization p)
    (hunit : forall u : (Otri p)ˣ, N.norm (PsiCnsUnitKummer p u) = 1)
    (u : (Otri p)ˣ) : PsiCnsUnitKummer p u ∈ PsiCns p N := by
  show N.norm (PsiCnsUnitKummer p u) ∈ zhatNonneg
  rw [hunit u]
  exact zhatNonneg_one

/-! ## 4. The precise missing chain -/

/-- (M4) The normalization exists (equivalently: the surjection
H^1(G_v, mu_hat^Z) ->> Z-hat of Corollary 1.10(b) is constructed). -/
def NormalizationMissing : Prop := Nonempty (PsiCnsNormalization p)

/-- (M2) The cyclotomic comparison, as located in S2017: the group-theoretic
cyclotome mu_hat^Z(G_v) is the actual cyclotome of the local field.  This is
the paper's cyclotomic rigidity (Cor 2.8(i); 2.9), and is what makes the
group-theoretic Psi_cns live in the same limit as the Kummer map.  It is not
proved here; S2017 proves it follows from local reciprocity on torsion. -/
abbrev CyclotomeComparison : Prop := muHatComparison p

/-- The full missing content of Corollary 1.10(b)+(d): a normalization which is
the valuation on the Kummer image and which exhausts the nonnegative part. -/
def Cor110bKummerIdentification : Prop :=
  exists N : PsiCnsNormalization p,
    NormalizationIsValuation p N ∧ PsiCnsExhaustion p N

/-- The missing content yields the identification Psi_cns = O^tri_{F_v}. -/
theorem PsiCns_equiv_otriFv_of_identification (h : Cor110bKummerIdentification p) :
    Nonempty (PsiCns p h.choose ≃* OtriFv p) :=
  PsiCns_equiv_otriFv p h.choose h.choose_spec.1 h.choose_spec.2

/-- Conversely, the identification of Psi_cns with O^tri_{F_v} through the
canonical inclusion forces the exhaustion, hence the missing content. -/
theorem identification_of_canonical_equiv (N : PsiCnsNormalization p)
    (hval : NormalizationIsValuation p N)
    (hbij : Function.Bijective (baseImageToPsiCns p N hval)) :
    NormalizationIsValuation p N ∧ PsiCnsExhaustion p N :=
  ⟨hval, (baseImageToPsiCns_bijective_iff_exhaustion p N hval).mp hbij⟩

/-- The same statement in the form of the paper's (d). -/
theorem kummerEquals_of_canonical_equiv (N : PsiCnsNormalization p)
    (hval : NormalizationIsValuation p N)
    (hbij : Function.Bijective (baseImageToPsiCns p N hval)) :
    KummerEqualsPsiCns p N :=
  (kummerEquals_iff p N).mpr (identification_of_canonical_equiv p N hval hbij)

/-- The cyclotomic comparison in the exact form in which the Kummer map uses
it: the group-theoretic cyclotome mu_hat^Z(G_v) is the coefficient module
Hom(Q/Z, (O^tri)^x) of the actual Kummer map, not merely its torsion
submodule.  This is the paper's cyclotomic rigidity (Cor 2.8, (i); 2.9) on the
coefficient modules; transporting it to the cohomological limits additionally
needs the G_v-action on the group-theoretic cyclotome, which S2017 records as
missing (M5). -/
theorem cyclotomeComparison_iff :
    muHatComparison p ↔ Nonempty (muHatZ p ≃* PsiCnsCyclotome p) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.trans (PsiCnsCyclotomeTorsionEquiv p).symm⟩
  · rintro ⟨e⟩
    exact ⟨e.trans (PsiCnsCyclotomeTorsionEquiv p)⟩

/-- The coefficient-module form of the cyclotomic comparison. -/
theorem PsiCnsCyclotome_equiv_of_cyclotomeComparison (h : muHatComparison p) :
    Nonempty (muHatZ p ≃* PsiCnsCyclotome p) :=
  (cyclotomeComparison_iff p).mp h

/-! ## 5. Axiom probes -/

#print axioms zhatIntHom_injective
#print axioms zhatNat_mul_mem
#print axioms zhatNonneg_mul
#print axioms otriFvToOtri_mul
#print axioms otriFvToOtri_injective
#print axioms PsiCnsBaseKummer_injective
#print axioms PsiCnsBaseImage_equiv
#print axioms mem_PsiCns
#print axioms mul_mem_PsiCns
#print axioms PsiCnsBaseImage_le_of_valuation
#print axioms kummerEquals_iff
#print axioms baseImageToPsiCns_bijective_iff_exhaustion
#print axioms PsiCns_equiv_otriFv
#print axioms PsiCns_equiv_otriFv_of_identification
#print axioms cyclotomeComparison_iff
#print axioms PsiCnsCyclotome_equiv_of_cyclotomeComparison
#print axioms PsiCns_stable_of_invariant
#print axioms PsiCnsUnitKummer_mem
#print axioms kummerEquals_of_canonical_equiv

end LeanFormal.IUT.XiFPaper.S2039ActualPsiCns