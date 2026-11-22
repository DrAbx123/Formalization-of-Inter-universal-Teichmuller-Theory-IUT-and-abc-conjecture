import LeanFormal.IUT.IUTII.Frobenioid.LocalUnitKummerMap
import LeanFormal.IUT.IUTII.Frobenioid.LocalUnitKummerInjectivity
import LeanFormal.IUT.IUTII.Frobenioid.LocalTorsionCyclotome

/-!
# S2000: the actual cohomological Psi_cns, its Kummer map, and the exact first missing

Layer: **O** (original Theta-link / q-pilot).  Consumer: the S1973 package
(tmp/sheaf/xif/paper/S1973PsiCnsActual.lean) and the S1975 joint-continuity
package.

## The paper object

IUT II, Proposition 4.1, (i), applies [AbsTopIII], Corollary 1.10, (b), to the
local absolute Galois group G_v and obtains a functorial group-theoretic
algorithm for the ind-topological submonoid

  Psi_cns(G_v) subset lim_J H^1(J, mu_hat^Z(G_v))

which is naturally isomorphic to O^tri_{F_v} and carries its natural
G_v-action.  Here J ranges over the open subgroups and, in [AbsTopIII],
Corollary 1.10, (a),

  mu_Q/Z(G_v) = colim_H (H^ab)_tors,
  mu_hat^Z(G_v) = Hom(Q/Z, mu_Q/Z(G_v)).

The source algorithm has three layers: (1) the group-theoretic construction of
the coefficient cyclotome and of H^2(G_v, mu_hat^Z) = Z-hat; (2) the resulting
surjection H^1(G_v, mu_hat^Z) -> Z-hat, whose inverse image of Z is the Kummer
image of k^times; (3) the identification of the inverse image of the
nonnegative part with O^tri.

## What this file constructs

The actual local-field cohomological side is constructed here, without
postulating the paper's abstract algorithm:

1. PsiCnsCyclotome p = Hom(Q/Z, (O^tri)^times), the actual cyclotome of the
   local integral monoid.  It is proved isomorphic to
   Hom(Q/Z, torsion (O^tri)^times) = Hom(Q/Z, mu); this is the genuine
   cyclotomic coefficient module, not an abstract placeholder.
2. PsiCnsCoefficientAction p, the actual continuous G_v-action on the
   cyclotome, and PsiCnsCohomology p = lim_J H^1(J, PsiCnsCyclotome p), the
   genuine direct limit of continuous first cohomology over the open subgroups
   of the local absolute Galois group (built on Iut.Foundations.ContinuousH1).
3. The actual Kummer map PsiCnsKummer p : O^tri -> PsiCnsCohomology p, defined
   for every nonzero integral element (not only for units), by the canonical
   compatible root system of its image in the Grothendieck group and the actual
   root-ratio cocycle.  Its multiplicativity and unit law are proved, and its
   image PsiCnsKummerImage p is an actual submonoid of the cohomology limit.
4. PsiCnsUnitKummer p: the restriction of the Kummer map to the units of O^tri.
   It is proved injective using the existing local integral-unit Kummer
   injectivity theorem, and therefore gives a genuine multiplicative
   equivalence (O^tri)^times ~= PsiCnsUnitKummerImage p.

## Exact first missing (no fake monoid, no axiom, no sorry)

The paper's [AbsTopIII], Corollary 1.10, (b), **group-theoretic** construction
of mu_hat^Z(G_v) from the topological group G_v alone, its H^2-normalization,
and the resulting identification of the abstract Psi_cns(G_v) with the actual
Kummer image constructed above, is **not** formalized.  In particular this file
does not assert that PsiCnsKummerImage p is the paper's Psi_cns(G_v).

For the actual model the single concrete statement still needed to identify
the Kummer image with O^tri is PsiCnsKummerKernelInUnits p: every
Grothendieck-group element with trivial Kummer germ is already a unit of O^tri.
It is stated, not assumed and not proved.  We prove that it is equivalent to
full injectivity of PsiCnsKummer p and hence to the monoid identification
PsiCnsKummerImage p ~= O^tri.  Thus this is a genuine missing theorem about the
actual map, not a packaging of the conclusion.

The G_v-action on the cohomological limit and the joint continuity of the
action are not constructed here; the pointwise action on the IndIntegralMonoid
model and the exact joint-continuity statement remain those of S1973/S1975.

No sorry, axiom, True/PUnit slot, empty type, arbitrary inhabitant, or
assumption-only Nonempty gate is used.
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.LocalMLFModelTMPair

namespace LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual

/-! ## 0. The actual local carriers and the actual cyclotome -/

/-- The actual local absolute Galois group at the rational prime p
(i.e. G_v for a rational finite place with residue characteristic p). -/
abbrev Gv (p : Nat) [Fact (Nat.Prime p)] : Type := LocalAbsoluteGalois p

/-- The actual nonzero integral monoid O^tri of the local algebraic closure.
This is the carrier of the S1973 PsiCnsModel after the canonical completion
identification; it is the same nonzero-integral-closure type, not a model
invented for this file. -/
abbrev Otri (p : Nat) [Fact (Nat.Prime p)] : Type := LocalIntegralMonoid p

/-- The actual nonzero integral monoid model.  This is the same
nonzero-integral-closure monoid as the S1973 PsiCnsModel, on the standard
Q_p model of the local field; the canonical completion identification is the
one already used by S1973 to compare the two carriers. -/
abbrev PsiCnsModel (p : Nat) [Fact (Nat.Prime p)] : Type := Otri p

/-- The actual coefficient cyclotome Hom(Q/Z, (O^tri)^times).  This is
mu_hat^Z realized on the actual local integral monoid. -/
abbrev PsiCnsCyclotome (p : Nat) [Fact (Nat.Prime p)] : Type :=
  KummerCyclotome (Otri p)ˣ

/-- The cyclotome with coefficients restricted to the actual roots of unity,
i.e. Hom(Q/Z, mu). -/
abbrev PsiCnsTorsionCyclotome (p : Nat) [Fact (Nat.Prime p)] : Type :=
  KummerCyclotome (CommGroup.torsion (Otri p)ˣ)

/-- Every hom from Q/Z into the units of the local integral monoid lands in the
torsion subgroup.  This proves that PsiCnsCyclotome is literally the paper's
Hom(Q/Z, mu)-cyclotome, not a larger unit group. -/
noncomputable def torsionCorestrict (p : Nat) [Fact (Nat.Prime p)]
    (f : PsiCnsCyclotome p) : PsiCnsTorsionCyclotome p where
  toFun q :=
    ⟨f q, (CommGroup.mem_torsion (f q)).mpr
      (f.isOfFinOrder (RationalCircleCyclotome.rationalCircle_isOfFinOrder q))⟩
  map_one' := by
    apply Subtype.ext
    exact map_one f
  map_mul' q r := by
    apply Subtype.ext
    exact map_mul f q r

/-- Precomposition with the inclusion of the torsion units. -/
noncomputable def torsionPrecompose (p : Nat) [Fact (Nat.Prime p)]
    (f : PsiCnsTorsionCyclotome p) : PsiCnsCyclotome p :=
  (Subgroup.subtype (CommGroup.torsion (Otri p)ˣ)).comp f

theorem torsionCorestrict_precompose (p : Nat) [Fact (Nat.Prime p)]
    (f : PsiCnsTorsionCyclotome p) :
    torsionCorestrict p (torsionPrecompose p f) = f := by
  apply MonoidHom.ext
  intro q
  apply Subtype.ext
  rfl

theorem torsionPrecompose_corestrict (p : Nat) [Fact (Nat.Prime p)]
    (f : PsiCnsCyclotome p) :
    torsionPrecompose p (torsionCorestrict p f) = f := by
  apply MonoidHom.ext
  intro q
  rfl

/-- The actual cyclotome is exactly Hom(Q/Z, mu). -/
noncomputable def PsiCnsCyclotomeTorsionEquiv (p : Nat) [Fact (Nat.Prime p)] :
    PsiCnsCyclotome p ≃* PsiCnsTorsionCyclotome p where
  toFun := torsionCorestrict p
  invFun := torsionPrecompose p
  left_inv := torsionPrecompose_corestrict p
  right_inv := torsionCorestrict_precompose p
  map_mul' f g := by
    apply MonoidHom.ext
    intro q
    apply Subtype.ext
    rfl

/-! ## 1. The cohomological limit over the open subgroups -/

/-- The actual continuous G_v-action on the coefficient cyclotome, induced
from the action on the integral units. -/
abbrev PsiCnsCoefficientAction (p : Nat) [Fact (Nat.Prime p)] :
    Iut.ContinuousGroupAction (Gv p) (PsiCnsCyclotome p) :=
  KummerCyclotome.continuousAction ((monoAnalytic p).discreteIntegralUnitAction p)

/-- The actual cohomological limit lim_J H^1(J, mu_hat^Z), presented as
continuous cocycle germs over the open subgroups of G_v. -/
abbrev PsiCnsCohomology (p : Nat) [Fact (Nat.Prime p)] : Type :=
  Iut.ContinuousH1Germ (PsiCnsCoefficientAction p)

/-! ## 2. The actual Kummer map on all of O^tri -/

/-- The actual Kummer germ of a nonzero integral element.  The construction uses
the canonical compatible rational root system in the Grothendieck group and the
actual integral-unit root-ratio cocycle; it is defined for every integral
element, not only for units. -/
noncomputable def PsiCnsKummerGerm (p : Nat) [Fact (Nat.Prime p)]
    (value : Otri p) : PsiCnsCohomology p :=
  (canonicalIntegralKummerRootRealization p (monoAnalytic p) value).germ

/-- The actual Kummer germ is multiplicative on the integral monoid. -/
theorem PsiCnsKummerGerm_mul (p : Nat) [Fact (Nat.Prime p)]
    (first second : Otri p) :
    PsiCnsKummerGerm p (first * second) =
      PsiCnsKummerGerm p first * PsiCnsKummerGerm p second := by
  let firstRealization :=
    canonicalIntegralKummerRootRealization p (monoAnalytic p) first
  let secondRealization :=
    canonicalIntegralKummerRootRealization p (monoAnalytic p) second
  let productRealization := firstRealization.mul secondRealization
  let canonicalProduct :=
    canonicalIntegralKummerRootRealization p (monoAnalytic p) (first * second)
  exact (canonicalProduct.germ_eq productRealization).trans (by
    change productRealization.germ =
      PsiCnsKummerGerm p first * PsiCnsKummerGerm p second
    exact firstRealization.mul_germ secondRealization)

/-- The Kummer germ of 1 is the identity class. -/
theorem PsiCnsKummerGerm_one (p : Nat) [Fact (Nat.Prime p)] :
    PsiCnsKummerGerm p 1 = 1 := by
  have productIdentity := PsiCnsKummerGerm_mul p 1 1
  have idempotent :
      PsiCnsKummerGerm p 1 =
        PsiCnsKummerGerm p 1 * PsiCnsKummerGerm p 1 := by
    simpa only [one_mul] using productIdentity
  have cancellable :
      PsiCnsKummerGerm p 1 * 1 =
        PsiCnsKummerGerm p 1 * PsiCnsKummerGerm p 1 := by
    simpa only [mul_one] using idempotent
  exact (mul_left_cancel cancellable).symm

/-- The actual Kummer map O^tri -> lim_J H^1(J, mu_hat^Z). -/
noncomputable def PsiCnsKummer (p : Nat) [Fact (Nat.Prime p)] :
    Otri p →* PsiCnsCohomology p where
  toFun := PsiCnsKummerGerm p
  map_one' := PsiCnsKummerGerm_one p
  map_mul' := PsiCnsKummerGerm_mul p

/-- The actual submonoid of the cohomological limit obtained as the Kummer
image of O^tri.  This is a genuine submonoid of the direct limit, not a
placeholder for the paper's Psi_cns. -/
noncomputable abbrev PsiCnsKummerImage (p : Nat) [Fact (Nat.Prime p)] :
    Submonoid (PsiCnsCohomology p) :=
  MonoidHom.mrange (PsiCnsKummer p)

/-! ## 3. The unit part: an unconditional isomorphism -/

/-- The restriction of the actual Kummer map to the units of O^tri. -/
noncomputable def PsiCnsUnitKummer (p : Nat) [Fact (Nat.Prime p)] :
    (Otri p)ˣ →* PsiCnsCohomology p where
  toFun u := PsiCnsKummer p (u : Otri p)
  map_one' := by simp
  map_mul' u v := by simp

/-- The unit Kummer map is the existing local integral-unit Kummer map. -/
theorem PsiCnsUnitKummer_eq (p : Nat) [Fact (Nat.Prime p)] :
    PsiCnsUnitKummer p = integralUnitKummerHom p (monoAnalytic p) := by
  apply MonoidHom.ext
  intro u
  rfl

/-- The actual unit Kummer map is injective.  This is the existing
residually-finite/fixed-field Kummer injectivity theorem, transported to the
present carrier. -/
theorem PsiCnsUnitKummer_injective (p : Nat) [Fact (Nat.Prime p)] :
    Function.Injective (PsiCnsUnitKummer p) := by
  rw [PsiCnsUnitKummer_eq p]
  exact LocalIntegralUnitKummerInjectivity.monoAnalytic_integralUnitKummerHom_injective p

/-- A unit has trivial Kummer class exactly when it is the identity unit. -/
theorem PsiCnsUnitKummer_eq_one_iff (p : Nat) [Fact (Nat.Prime p)]
    (u : (Otri p)ˣ) : PsiCnsUnitKummer p u = 1 ↔ u = 1 := by
  constructor
  · intro h
    apply PsiCnsUnitKummer_injective p
    simpa using h
  · intro h
    subst h
    exact map_one (PsiCnsUnitKummer p)

/-- The image of the unit Kummer map in the cohomological limit. -/
noncomputable abbrev PsiCnsUnitKummerImage (p : Nat) [Fact (Nat.Prime p)] :
    Submonoid (PsiCnsCohomology p) :=
  MonoidHom.mrange (PsiCnsUnitKummer p)

/-- The unit Kummer image is literally a submonoid of the full Kummer image. -/
theorem PsiCnsUnitKummerImage_le (p : Nat) [Fact (Nat.Prime p)] :
    PsiCnsUnitKummerImage p ≤ PsiCnsKummerImage p := by
  rintro x ⟨u, rfl⟩
  exact ⟨(u : Otri p), rfl⟩

/-- The unit part of the actual Kummer image is isomorphic to the actual unit
group.  This is an unconditional identification, not the paper's full
O^tri-identification. -/
noncomputable def PsiCnsUnitKummerEquiv (p : Nat) [Fact (Nat.Prime p)] :
    (Otri p)ˣ ≃* PsiCnsUnitKummerImage p := by
  let e : (Otri p)ˣ →* PsiCnsUnitKummerImage p :=
    (PsiCnsUnitKummer p).mrangeRestrict
  have hb : Function.Bijective e := by
    constructor
    · intro x y hxy
      apply PsiCnsUnitKummer_injective p
      exact congrArg Subtype.val hxy
    · exact MonoidHom.mrangeRestrict_surjective (PsiCnsUnitKummer p)
  exact MulEquiv.ofBijective e hb

/-! ## 4. The exact concrete first missing for the full identification -/

/-- The extension of the actual Kummer map to the Grothendieck group
Qbar_p^times of the integral monoid. -/
noncomputable def PsiCnsKummerGroupification (p : Nat) [Fact (Nat.Prime p)] :
    LocalGroupification p →* PsiCnsCohomology p :=
  Algebra.GrothendieckGroup.lift (PsiCnsKummer p)

@[simp] theorem PsiCnsKummerGroupification_of (p : Nat) [Fact (Nat.Prime p)]
    (value : Otri p) :
    PsiCnsKummerGroupification p (Algebra.GrothendieckGroup.of value) =
      PsiCnsKummer p value := by
  let universalProperty :=
    Equiv.symm_apply_apply
      (Algebra.GrothendieckGroup.lift
        (M := Otri p) (G := PsiCnsCohomology p))
      (PsiCnsKummer p)
  change
    (Algebra.GrothendieckGroup.lift (PsiCnsKummer p)).comp
        Algebra.GrothendieckGroup.of =
      PsiCnsKummer p at universalProperty
  exact DFunLike.congr_fun universalProperty value

@[simp] theorem PsiCnsKummerGroupification_unit (p : Nat) [Fact (Nat.Prime p)]
    (u : (Otri p)ˣ) :
    PsiCnsKummerGroupification p (unitGrothendieckHom p u) =
      PsiCnsUnitKummer p u := by
  change PsiCnsKummerGroupification p
      (Algebra.GrothendieckGroup.of (u : Otri p)) = _
  rw [PsiCnsKummerGroupification_of]
  rfl

/-- **The exact concrete first missing.**  Every element of the actual
Grothendieck group with trivial Kummer class is already a unit of the nonzero
integral monoid.  Equivalently, the Kummer map detects the non-integral
(uniformizer) direction.  This is the actual valuation/cyclotomic assertion
that remains after the cohomological construction.

It is stated as a proposition, not assumed.  The theorem below proves that it
implies full injectivity of the Kummer map and hence the monoid identification
of its image with O^tri. -/
def PsiCnsKummerKernelInUnits (p : Nat) [Fact (Nat.Prime p)] : Prop :=
  ∀ x : LocalGroupification p, PsiCnsKummerGroupification p x = 1 →
    ∃ u : (Otri p)ˣ, unitGrothendieckHom p u = x

/-- If the kernel of the groupified Kummer map is contained in the units, then
the actual Kummer map on O^tri is injective. -/
theorem PsiCnsKummer_injective_of_kernelInUnits (p : Nat) [Fact (Nat.Prime p)]
    (h : PsiCnsKummerKernelInUnits p) :
    Function.Injective (PsiCnsKummer p) := by
  intro a b hab
  have hF : PsiCnsKummerGroupification p
      (Algebra.GrothendieckGroup.of a / Algebra.GrothendieckGroup.of b) = 1 := by
    rw [map_div, PsiCnsKummerGroupification_of,
      PsiCnsKummerGroupification_of, hab]
    exact div_self' _
  obtain ⟨u, hu⟩ := h _ hF
  have hfu : PsiCnsUnitKummer p u = 1 := by
    have hof : PsiCnsKummerGroupification p
        (unitGrothendieckHom p u) = 1 := by
      rw [hu]
      exact hF
    simpa using hof
  have hu1 : u = 1 := PsiCnsUnitKummer_injective p (by simpa using hfu)
  have hdiv :
      Algebra.GrothendieckGroup.of a / Algebra.GrothendieckGroup.of b = 1 := by
    rw [← hu, hu1, map_one]
  have hofeq :
      Algebra.GrothendieckGroup.of a = Algebra.GrothendieckGroup.of b :=
    div_eq_one.mp hdiv
  have htrans := congrArg
    (LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p) hofeq
  change LocalIntegralMonoid.groupificationToAlgebraicClosureUnits p
      (Algebra.GrothendieckGroup.of a) =
    LocalIntegralMonoid.groupificationToAlgebraicClosureUnits p
      (Algebra.GrothendieckGroup.of b) at htrans
  rw [LocalIntegralMonoid.groupificationToAlgebraicClosureUnits_of,
    LocalIntegralMonoid.groupificationToAlgebraicClosureUnits_of] at htrans
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg Units.val htrans

/-- Conversely, full injectivity of the actual Kummer map forces the kernel of
its groupification to lie in the units. -/
theorem PsiCnsKummerKernelInUnits_of_injective
    (p : Nat) [Fact (Nat.Prime p)]
    (h : Function.Injective (PsiCnsKummer p)) :
    PsiCnsKummerKernelInUnits p := by
  intro x hx
  let f := (Localization.monoidOf (⊤ : Submonoid (Otri p)))
  let s := f.sec x
  have hf : PsiCnsKummer p s.1 = PsiCnsKummer p s.2 := by
    have hx' : PsiCnsKummerGroupification p x = 1 := hx
    rw [PsiCnsKummerGroupification, Algebra.GrothendieckGroup.lift_apply] at hx'
    exact div_eq_one.mp hx'
  have hsec : s.1 = s.2 := h hf
  refine ⟨1, ?_⟩
  have hx1 : x = 1 := by
    have hspec := f.sec_spec x
    rw [hsec] at hspec
    have hcancel : x * f s.2 =
        (1 : Localization (⊤ : Submonoid (Otri p))) * f s.2 := by
      rw [one_mul]
      exact hspec
    exact mul_right_cancel hcancel
  rw [hx1, map_one]

/-- The concrete missing statement is exactly full injectivity of the actual
Kummer map. -/
theorem PsiCnsKummerKernelInUnits_iff_injective
    (p : Nat) [Fact (Nat.Prime p)] :
    PsiCnsKummerKernelInUnits p ↔ Function.Injective (PsiCnsKummer p) :=
  ⟨PsiCnsKummer_injective_of_kernelInUnits p,
    PsiCnsKummerKernelInUnits_of_injective p⟩

/-- The conditional paper-shape identification: if the concrete missing
statement holds, the actual Kummer image is multiplicatively equivalent to the
actual nonzero integral monoid O^tri (equivalently to the S1973
IndIntegralMonoid model on the identified carrier). -/
theorem PsiCnsKummerImage_equiv_of_kernelInUnits
    (p : Nat) [Fact (Nat.Prime p)] (h : PsiCnsKummerKernelInUnits p) :
    Nonempty (PsiCnsKummerImage p ≃* PsiCnsModel p) := by
  have hinj := PsiCnsKummer_injective_of_kernelInUnits p h
  let e : Otri p →* PsiCnsKummerImage p :=
    (PsiCnsKummer p).mrangeRestrict
  have hb : Function.Bijective e := by
    constructor
    · intro x y hxy
      apply hinj
      exact congrArg Subtype.val hxy
    · exact MonoidHom.mrangeRestrict_surjective (PsiCnsKummer p)
  exact ⟨(MulEquiv.ofBijective e hb).symm⟩

/-! ## 5. Axiom probes -/

#print axioms PsiCnsCyclotomeTorsionEquiv
#print axioms PsiCnsKummerGerm_mul
#print axioms PsiCnsKummerGerm_one
#print axioms PsiCnsUnitKummer_injective
#print axioms PsiCnsUnitKummer_eq_one_iff
#print axioms PsiCnsUnitKummerEquiv
#print axioms PsiCnsKummer_injective_of_kernelInUnits
#print axioms PsiCnsKummerKernelInUnits_of_injective
#print axioms PsiCnsKummerKernelInUnits_iff_injective
#print axioms PsiCnsKummerImage_equiv_of_kernelInUnits

end LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
