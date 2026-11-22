import tmp.sheaf.xif.paper.S2027LocalArtinActual
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Tactic.Group

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false

noncomputable section
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2011Cor110bActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2024LocalReciprocityActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual

namespace LeanFormal.IUT.XiFPaper.S2036ActualPsiCnsM234Actual

variable (p : Nat) [Fact (Nat.Prime p)]

/-! ## 1. The profinite integers Z-hat -/

def ZhatCompatible (x : (n : ℕ+) → ZMod n) : Prop :=
  ∀ (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ)),
    ZMod.castHom h (ZMod m) (x n) = x m

def zhatSubring : Subring ((n : ℕ+) → ZMod n) where
  carrier := {x | ZhatCompatible x}
  zero_mem' := by
    intro m n h
    exact map_zero (ZMod.castHom h (ZMod m))
  one_mem' := by
    intro m n h
    exact map_one (ZMod.castHom h (ZMod m))
  add_mem' := by
    intro x y hx hy m n hmn
    rw [Pi.add_apply, Pi.add_apply, map_add, hx m n hmn, hy m n hmn]
  mul_mem' := by
    intro x y hx hy m n hmn
    rw [Pi.mul_apply, Pi.mul_apply, map_mul, hx m n hmn, hy m n hmn]
  neg_mem' := by
    intro x hx m n hmn
    rw [Pi.neg_apply, Pi.neg_apply, map_neg, hx m n hmn]

abbrev Zhat : Type := zhatSubring

instance : CommRing Zhat := zhatSubring.toCommRing

@[ext] theorem Zhat.ext {x y : Zhat}
    (h : ∀ n : ℕ+, (x : (n : ℕ+) → ZMod n) n = (y : (n : ℕ+) → ZMod n) n) :
    x = y := by
  apply Subtype.ext
  funext n
  exact h n

def zhatEval (n : ℕ+) : Zhat →+* ZMod n where
  toFun x := (x : (k : ℕ+) → ZMod k) n
  map_one' := rfl
  map_zero' := rfl
  map_add' x y := rfl
  map_mul' x y := rfl

theorem zhat_one_ne_zero : (1 : Zhat) ≠ 0 := by
  intro h
  have h2 := congrArg (zhatEval 2) h
  change (1 : ZMod 2) = 0 at h2
  exact (one_ne_zero : (1 : ZMod 2) ≠ 0) h2

instance : Nontrivial Zhat :=
  ⟨⟨1, 0, zhat_one_ne_zero⟩⟩

def intCastZhat : ℤ →+* Zhat where
  toFun z :=
    ⟨fun n => (z : ZMod n), by
      intro m n h
      exact map_intCast (ZMod.castHom h (ZMod m)) z⟩
  map_zero' := by
    apply Zhat.ext
    intro n
    exact map_zero (Int.castRingHom (ZMod n))
  map_one' := by
    apply Zhat.ext
    intro n
    exact map_one (Int.castRingHom (ZMod n))
  map_add' x y := by
    apply Zhat.ext
    intro n
    exact map_add (Int.castRingHom (ZMod n)) x y
  map_mul' x y := by
    apply Zhat.ext
    intro n
    exact map_mul (Int.castRingHom (ZMod n)) x y

def zhatFrobeniusSubgroup : Subgroup (Multiplicative Zhat) :=
  Subgroup.closure {Multiplicative.ofAdd (1 : Zhat)}

def zhatNatMonoid : Submonoid (Multiplicative Zhat) :=
  Submonoid.closure {Multiplicative.ofAdd (1 : Zhat)}

theorem zhatNatMonoid_subset_frobenius :
    ∀ x ∈ zhatNatMonoid, x ∈ zhatFrobeniusSubgroup := by
  intro x hx
  refine Submonoid.closure_induction_left
    (motive := fun y _ => y ∈ zhatFrobeniusSubgroup) ?_ ?_ hx
  · exact Subgroup.one_mem _
  · intro a ha b _ ih
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ha) ih

/-! ## 2. Continuous H^2 for an arbitrary continuous action -/

section ContinuousH2

universe u

variable {G A : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
  (action : Iut.ContinuousGroupAction G A)

/-- Continuous functions on a topological space with values in a topological
abelian group, as a subgroup of the full function group. -/
def continuousFunctionSubgroup (X : Type u) [TopologicalSpace X] :
    Subgroup (X → A) where
  carrier := {f | Continuous f}
  one_mem' := continuous_const
  mul_mem' hf hg := hf.mul hg
  inv_mem' hf := hf.inv

abbrev ContinuousOneCochain : Type u := continuousFunctionSubgroup (A := A) G
abbrev ContinuousTwoCochain : Type u := continuousFunctionSubgroup (A := A) (G × G)
abbrev ContinuousThreeCochain : Type u := continuousFunctionSubgroup (A := A) (G × G × G)

@[ext] theorem ContinuousTwoCochain.ext {f g : ContinuousTwoCochain (G := G) (A := A)}
    (h : ∀ x y, f.1 (x, y) = g.1 (x, y)) : f = g := by
  apply Subtype.ext
  funext p
  exact h p.1 p.2

/-- The first differential on continuous cochains. -/
def deltaOne : ContinuousOneCochain (G := G) (A := A) →*
    ContinuousTwoCochain (G := G) (A := A) where
  toFun a :=
    ⟨fun p : G × G => a.1 p.1 * action.act p.1 (a.1 p.2) * (a.1 (p.1 * p.2))⁻¹, by
      have h1 : Continuous fun p : G × G => a.1 p.1 := a.2.comp continuous_fst
      have h2 : Continuous fun p : G × G => action.act p.1 (a.1 p.2) :=
        action.continuous_action.comp
          (continuous_fst.prodMk (a.2.comp continuous_snd))
      have h3 : Continuous fun p : G × G => (a.1 (p.1 * p.2))⁻¹ :=
        (a.2.comp (continuous_fst.mul continuous_snd)).inv
      exact (h1.mul h2).mul h3⟩
  map_one' := by
    apply ContinuousTwoCochain.ext
    intro g h
    simp
  map_mul' a b := by
    apply ContinuousTwoCochain.ext
    intro g h
    change (a.1 g * b.1 g) * action.act g (a.1 h * b.1 h) *
        (a.1 (g * h) * b.1 (g * h))⁻¹ =
      (a.1 g * action.act g (a.1 h) * (a.1 (g * h))⁻¹) *
        (b.1 g * action.act g (b.1 h) * (b.1 (g * h))⁻¹)
    rw [Iut.ContinuousGroupAction.act_mul]
    simp [mul_comm, mul_left_comm, mul_assoc]

/-- The second differential on continuous cochains. -/
def deltaTwo : ContinuousTwoCochain (G := G) (A := A) →*
    ContinuousThreeCochain (G := G) (A := A) where
  toFun c :=
    ⟨fun p : G × G × G =>
        action.act p.1 (c.1 (p.2.1, p.2.2)) * c.1 (p.1, p.2.1 * p.2.2) *
          (c.1 (p.1, p.2.1) * c.1 (p.1 * p.2.1, p.2.2))⁻¹, by
      have h1 : Continuous fun p : G × G × G =>
          action.act p.1 (c.1 (p.2.1, p.2.2)) :=
        action.continuous_action.comp
          (continuous_fst.prodMk
            (c.2.comp ((continuous_fst.comp continuous_snd).prodMk
              (continuous_snd.comp continuous_snd))))
      have h2 : Continuous fun p : G × G × G => c.1 (p.1, p.2.1 * p.2.2) :=
        c.2.comp (continuous_fst.prodMk
          ((continuous_fst.comp continuous_snd).mul
            (continuous_snd.comp continuous_snd)))
      have h3 : Continuous fun p : G × G × G => c.1 (p.1, p.2.1) :=
        c.2.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
      have h4 : Continuous fun p : G × G × G => c.1 (p.1 * p.2.1, p.2.2) :=
        c.2.comp ((continuous_fst.mul (continuous_fst.comp continuous_snd)).prodMk
          (continuous_snd.comp continuous_snd))
      exact (h1.mul h2).mul ((h3.mul h4).inv)⟩
  map_one' := by
    apply Subtype.ext
    funext p
    obtain ⟨g, h, k⟩ := p
    simp
  map_mul' c d := by
    apply Subtype.ext
    funext p
    obtain ⟨g, h, k⟩ := p
    change action.act g (c.1 (h, k) * d.1 (h, k)) *
        (c.1 (g, h * k) * d.1 (g, h * k)) *
        ((c.1 (g, h) * d.1 (g, h)) * (c.1 (g * h, k) * d.1 (g * h, k)))⁻¹ =
      (action.act g (c.1 (h, k)) * c.1 (g, h * k) *
          (c.1 (g, h) * c.1 (g * h, k))⁻¹) *
        (action.act g (d.1 (h, k)) * d.1 (g, h * k) *
          (d.1 (g, h) * d.1 (g * h, k))⁻¹)
    rw [Iut.ContinuousGroupAction.act_mul]
    simp [mul_comm, mul_left_comm, mul_assoc]

/-- The group of continuous 2-cocycles: the kernel of the second differential. -/
def twoCocycleSubgroup : Subgroup (ContinuousTwoCochain (G := G) (A := A)) :=
  (deltaTwo action).ker

abbrev ContinuousTwoCocycle : Type u := twoCocycleSubgroup action

/-- The standard 2-cocycle identity, exposed on the kernel of the second
differential. -/
theorem mem_twoCocycle_iff (c : ContinuousTwoCochain (G := G) (A := A)) :
    c ∈ twoCocycleSubgroup (action := action) ↔
      ∀ g h k, action.act g (c.1 (h, k)) * c.1 (g, h * k) =
        c.1 (g, h) * c.1 (g * h, k) := by
  constructor
  · intro hc g h k
    have hker := MonoidHom.mem_ker.mp hc
    have hv := congrArg (fun z : ContinuousThreeCochain (G := G) (A := A) =>
      z.1 (g, h, k)) hker
    simp only [deltaTwo, MonoidHom.coe_mk, OneHom.coe_mk, Pi.one_apply] at hv
    have hcancel := congrArg (fun z => z * (c.1 (g, h) * c.1 (g * h, k))) hv
    simpa [mul_assoc] using hcancel
  · intro hc
    change c ∈ (deltaTwo action).ker
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    funext p
    obtain ⟨g, h, k⟩ := p
    simp only [deltaTwo, MonoidHom.coe_mk, OneHom.coe_mk, Pi.one_apply]
    rw [hc g h k, mul_inv_cancel]
    rfl

/-- The continuous coboundary map attached to a continuous 1-cochain. -/
def deltaOneCocycle : ContinuousOneCochain (G := G) (A := A) →*
    ContinuousTwoCocycle (action := action) where
  toFun a :=
    ⟨deltaOne action a, by
      rw [mem_twoCocycle_iff]
      intro g h k
      change action.act g (a.1 h * action.act h (a.1 k) * (a.1 (h * k))⁻¹) *
          (a.1 g * action.act g (a.1 (h * k)) * (a.1 (g * (h * k)))⁻¹) =
        (a.1 g * action.act g (a.1 h) * (a.1 (g * h))⁻¹) *
          (a.1 (g * h) * action.act (g * h) (a.1 k) * (a.1 ((g * h) * k))⁻¹)
      rw [Iut.ContinuousGroupAction.act_mul, Iut.ContinuousGroupAction.act_mul,
        Iut.ContinuousGroupAction.act_inv,
        ← Iut.ContinuousGroupAction.act_mul_group,
        mul_assoc g h k]
      simp [mul_comm, mul_left_comm, mul_assoc]⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (deltaOne action)
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul (deltaOne action) a b

/-- The subgroup of continuous coboundaries inside the continuous 2-cocycles. -/
abbrev coboundarySubgroup : Subgroup (ContinuousTwoCocycle (action := action)) :=
  MonoidHom.range (deltaOneCocycle (action := action))

/-- **Continuous H^2**: continuous 2-cocycles modulo continuous coboundaries. -/
abbrev ContinuousH2 : Type u :=
  ContinuousTwoCocycle (action := action) ⧸ coboundarySubgroup (action := action)

end ContinuousH2

/-! ## 3. The actual H^2 carrier and the actual cyclotome -/

/-- **The actual continuous H^2 of G_v with coefficients in the actual
cyclotome** Hom(Q/Z, mu).  This is the cohomological carrier of M3. -/
abbrev PsiCnsH2 (p : Nat) [Fact (Nat.Prime p)] : Type :=
  ContinuousH2 (PsiCnsCoefficientAction p)

/-- The endomorphism monoid of the rational circle Q/Z, multiplicatively. -/
abbrev EndRationalCircle : Type :=
  Multiplicative (AddCircle (1 : ℚ)) →* Multiplicative (AddCircle (1 : ℚ))

/-- **The actual cyclotome is Hom(Q/Z, Q/Z).**  This composes the actual
torsion cyclotomic equivalence of the local integral monoid with the
Kummer-cyclotome functor.  It is unconditional and does not use the
IndIntegralMonoid model as a cohomological Psi_cns. -/
noncomputable def PsiCnsTorsionCyclotomeEquivEnd
    (p : Nat) [Fact (Nat.Prime p)] :
    PsiCnsTorsionCyclotome p ≃* EndRationalCircle :=
  kummerCyclotomeCongr (LocalIntegralMonoid.torsionCyclotomicEquiv p)

/-- **The actual cyclotome is the endomorphism monoid of Q/Z.** -/
noncomputable def PsiCnsCyclotomeEquivEnd
    (p : Nat) [Fact (Nat.Prime p)] :
    PsiCnsCyclotome p ≃* EndRationalCircle :=
  (PsiCnsCyclotomeTorsionEquiv p).trans (PsiCnsTorsionCyclotomeEquivEnd p)

/-! ## 4. M2: local reciprocity on torsion and the exact first missing -/

/-- (M2a) The local Artin map on torsion at every open subgroup, on the
profinite abelianization carrier.  This is S2027's localArtinTorsionTopological,
quantified over the open subgroups. -/
def LocalArtinTorsionInput (p : Nat) [Fact (Nat.Prime p)] : Prop :=
  ∀ U : Index p, localArtinTorsionTopological p U

/-- (M2c) The comparison between the abstract abelianization of S2011/S2024
and the profinite abelianization of the actual local Galois group. -/
def ProfiniteCarrierInput (p : Nat) [Fact (Nat.Prime p)] : Prop :=
  ∀ U : Index p, profiniteTorsionComparison p U

/-- **(M2), as the conjunction of its two missing inputs.**  This is the
first missing layer in dependency order; it is a proposition, never an
assumption field of a structure. -/
def M2FirstMissing (p : Nat) [Fact (Nat.Prime p)] : Prop :=
  LocalArtinTorsionInput p ∧ ProfiniteCarrierInput p

theorem M2FirstMissing_iff :
    M2FirstMissing p ↔ LocalArtinTorsionInput p ∧ ProfiniteCarrierInput p :=
  Iff.rfl

/-- (M2) is equivalent to the existence of S2027's local Artin source datum. -/
theorem M2FirstMissing_iff_sourceData :
    M2FirstMissing p ↔ Nonempty (LocalArtinSourceData p) := by
  constructor
  · rintro ⟨hartin, hcarrier⟩
    classical
    exact ⟨{
      artin := fun U => (hartin U).some
      carrier := fun U => (hcarrier U).some }⟩
  · rintro ⟨d⟩
    exact ⟨fun U => ⟨d.artin U⟩, fun U => ⟨d.carrier U⟩⟩

/-- A chosen source datum attached to the M2 input. -/
noncomputable def chosenSourceData (h : M2FirstMissing p) :
    LocalArtinSourceData p :=
  Classical.choice (M2FirstMissing_iff_sourceData p |>.mp h)

/-- The transfer compatibility (M2b) for a local Artin source datum: under the
levelwise identifications, the Verlagerung corresponds to the inclusion of
the roots of unity of the two fixed fields. -/
def M2TransferCompatibility (d : LocalArtinSourceData p) : Prop :=
  ∀ {H K : Index p} (h : H ≤ K) (v : CommGroup.torsion (Abelianization K)),
    levelwiseEquiv p d H (torsionMap (verlagerungOpen p h) v) =
      fixedFieldTorsionUnitsInclusion p h (levelwiseEquiv p d K v)

/-- **M2 yields S2024's local reciprocity datum**, given the transfer
compatibility.  This is a transport of S2027's localReciprocityData_of_source
to the M2 interface. -/
noncomputable def localReciprocityData_of_M2
    (h : M2FirstMissing p)
    (htransfer : M2TransferCompatibility p (chosenSourceData p h)) :
    LocalReciprocityData p :=
  localReciprocityData_of_source p (chosenSourceData p h) htransfer

/-- **M2 yields S2017's muQZComparison.** -/
theorem muQZComparison_of_M2
    (h : M2FirstMissing p)
    (htransfer : M2TransferCompatibility p (chosenSourceData p h)) :
    muQZComparison p :=
  muQZComparison_of_data p (localReciprocityData_of_M2 p h htransfer)

/-- **M2 yields S2017's muHatComparison.** -/
theorem muHatComparison_of_M2
    (h : M2FirstMissing p)
    (htransfer : M2TransferCompatibility p (chosenSourceData p h)) :
    muHatComparison p :=
  muHatComparison_of_data p (localReciprocityData_of_M2 p h htransfer)

/-- The first missing input in dependency order is the local Artin map on
torsion: (M2a) alone is already the missing local class field theory. -/
def FirstMissingLocalArtinMap (p : Nat) [Fact (Nat.Prime p)] : Prop :=
  LocalArtinTorsionInput p

theorem firstMissingLocalArtinMap_of_M2 (h : M2FirstMissing p) :
    FirstMissingLocalArtinMap p :=
  h.1

/-! ## 5. M3: continuous H^2 and Z-hat -/

/-- **(M3): H^2(G_v, mu_hat^Z) is Z-hat**, stated on the actual cohomological
carrier PsiCnsH2 p constructed above.  This is a proposition; it has no
inhabitant in this file. -/
def PsiCnsH2Normalization (p : Nat) [Fact (Nat.Prime p)] : Prop :=
  Nonempty (PsiCnsH2 p ≃* Multiplicative Zhat)

theorem PsiCnsH2Normalization_iff (p : Nat) [Fact (Nat.Prime p)] :
    PsiCnsH2Normalization p ↔
      Nonempty (PsiCnsH2 p ≃* Multiplicative Zhat) :=
  Iff.rfl

/-! ## 6. M4: the normalization and the actual Kummer image -/

/-- **(M4): the normalized surjection and its comparison with the actual
Kummer image.**

There is a surjective homomorphism nu from the actual cohomological limit to
Z-hat such that

* the actual Kummer image of O^tri is exactly the inverse image under nu of
  the nonnegative cone zhatNatMonoid (this is Corollary 1.10, (d), on the
  actual carriers), and
* the kernel of nu on the actual Kummer image is exactly the unit subgroup
  (the valuation-zero part).

This is a proposition; it has no inhabitant in this file.  The source
constructs nu from the H^2 class of (M3) and the cup product, which is a
separate missing input. -/
def PsiCnsKummerNormalization (p : Nat) [Fact (Nat.Prime p)] : Prop :=
  ∃ nu : PsiCnsCohomology p →* Multiplicative Zhat,
    Function.Surjective nu ∧
      MonoidHom.mrange (PsiCnsKummer p) = Submonoid.comap nu zhatNatMonoid ∧
        (∀ a : Otri p, nu (PsiCnsKummer p a) = 1 ↔
          ∃ u : (Otri p)ˣ, (u : Otri p) = a)

/-- **The comparison consequence of M4.**  The actual Kummer image is
multiplicatively equivalent to the inverse image of the nonnegative cone.
The proof uses the unconditional injectivity of the actual Kummer map
(S2006), so it is a genuine comparison of the actual Kummer image with the
normalization, not a restatement of the conclusion. -/
theorem kummerImage_equiv_nonnegative_of_normalization
    (h : PsiCnsKummerNormalization p) :
    ∃ nu : PsiCnsCohomology p →* Multiplicative Zhat,
      Function.Surjective nu ∧
        Nonempty ((Otri p) ≃* Submonoid.comap nu zhatNatMonoid) := by
  obtain ⟨nu, hsurj, himage, hker⟩ := h
  refine ⟨nu, hsurj, ?_⟩
  classical
  let e : Otri p →* Submonoid.comap nu zhatNatMonoid :=
    { toFun := fun a =>
        ⟨PsiCnsKummer p a, by
          rw [← himage]
          exact ⟨a, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp }
  have hinj : Function.Injective e := by
    intro a b hab
    apply LeanFormal.IUT.XiFPaper.S2006KummerKernelActual.PsiCnsKummer_injective p
    exact congrArg Subtype.val hab
  have hsurj' : Function.Surjective e := by
    intro y
    have hy : y.1 ∈ MonoidHom.mrange (PsiCnsKummer p) := by
      rw [himage]
      exact y.2
    obtain ⟨a, ha⟩ := hy
    exact ⟨a, Subtype.ext ha⟩
  exact ⟨MulEquiv.ofBijective e ⟨hinj, hsurj'⟩⟩

/-- The kernel half of M4, stated separately: the normalization detects the
units of O^tri exactly. -/
theorem kummer_kernel_units_of_normalization
    (h : PsiCnsKummerNormalization p) :
    ∃ nu : PsiCnsCohomology p →* Multiplicative Zhat,
      ∀ a : Otri p, nu (PsiCnsKummer p a) = 1 ↔
        ∃ u : (Otri p)ˣ, (u : Otri p) = a := by
  obtain ⟨nu, hsurj, himage, hker⟩ := h
  exact ⟨nu, hker⟩

/-! ## 7. The layered missing statements -/

/-- The three missing layers of [AbsTopIII], Corollary 1.10, (b), on the
actual carriers, recorded as named propositions. -/
def Cor110bLayersMissing (p : Nat) [Fact (Nat.Prime p)] : Prop :=
  M2FirstMissing p ∧ PsiCnsH2Normalization p ∧ PsiCnsKummerNormalization p

end LeanFormal.IUT.XiFPaper.S2036ActualPsiCnsM234Actual
