/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S2584PrimeDegreeOneActual
import tmp.sheaf.xif.paper.S2587LocalizedResidueDataActual
import tmp.sheaf.xif.paper.S2590LocalizedPrimeContractionActual
import tmp.sheaf.xif.paper.S2591LocalizedResidueEquivActual
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.Ideal.Over

/-!
# S2591 (task L-A): concrete Ideal.quotientMap parameters for the L-side residue
isomorphism O_L/P ~= ZMod 613 at the chosen prime over 613

## The question

Can the L-side residue isomorphism at the chosen prime over 613 be written as a
concrete Ideal.quotientMap, and with which parameters?

Ideal.quotientMap (Mathlib, RingTheory.Ideal.Quotient.Operations) has parameters

    {I : Ideal R} (J : Ideal S) [I.IsTwoSided] [J.IsTwoSided] (f : R ->+* S)
      (hIJ : I <= J.comap f) : R / I ->+* S / J

so a concrete residue map needs R, I, T, J, f and the inclusion I <= J.comap f.
Below every candidate is instantiated with the actual objects of this tree, and the
resulting maps are checked by the kernel.

## The L side of this tree

L = S1720Field, C = O_L = RingOfIntegers S1720Field,
S = O_L[1/c] (the localization of S2565ConcreteIntegralClosureCActual).
The chosen prime over 613 is the witness prime of S2584PrimeDegreeOneActual:
W.p : Ideal C (lies over (613), residue field ZMod 613) and its extension
W.P = W.p.map (algebraMap C S), with
W.residueEquiv : C / W.p ~= ZMod 613,
W.residueEquivS : S / W.P ~= ZMod 613,
W.quotientEquiv : S / W.P ~= C / W.p.

## The concrete parameter sets that type

1. Witness form, O_L-side prime W.p:

       residueMapZC    : (Z / (613)) ->+* (C / W.p)
                          R = Z, I = span{613}, T = C, J = W.p, f = algebraMap Z C,
                          hIJ from W.p_liesOver.

2. Witness form, localized prime W.P:

       residueMapZS    : (Z / (613)) ->+* (S / W.P)
                          R = Z, I = span{613}, T = S, J = W.P, f = algebraMap Z S,
                          hIJ from W.P_liesOver.

       residueMapCS    : (C / W.p) ->+* (S / W.P)
                          R = C, I = W.p, T = S, J = W.P, f = algebraMap C S,
                          hIJ from W.P_liesOver_p.

       residueMapCSmap : (C / W.p) ->+* (S / W.p.map (algebraMap C S))
                          same as above with J = W.p.map (algebraMap C S) and
                          hIJ = Ideal.le_comap_map (no LiesOver needed).

       residueMapLocalized : (C / W.P.comap (algebraMap C S)) ->+* (S / W.P)
                          hIJ = le_rfl; this is the parameter shape used by
                          S2591LocalizedResidueEquivActual.S2591_localized_residue_equiv.

3. S2587LocalizedResidueDataS form (the datum of the parent chain, prime D.p in S):

       residueMapZL    : (Z / (613)) ->+* (S / D.p)
                          R = Z, I = span{613}, T = S, J = D.p, f = algebraMap Z S,
                          hIJ from the membership 613 in D.p (the datum has no
                          LiesOver field; Ideal.span_singleton_le_iff_mem is enough).

4. ZMod 613 versions are obtained by composing with
   Int.quotientSpanNatEquivZMod 613 : (Z / (613)) ~= ZMod 613; the isomorphism
   itself is the witness field W.residueEquiv / W.residueEquivS.

No sorry, axiom, True, PUnit or native_decide is used.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace LeanFormal.IUT.XiFPaper.S2591ResidueIsoProbeActual

open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2587LocalizedResidueDataActual

/-- O_L: the ring of integers of the L-side field L = S1720Field. -/
abbrev C : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.C

/-- O_L[1/c]: the localized L-side ring of S2565. -/
abbrev S : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.S

/-! ## 1. The API shapes -/

#check Ideal.quotientMap
#check Ideal.Quotient.lift
#check Ideal.quotientEquiv
#check Ideal.quotientMap_mk
#check Ideal.quotientMap_injective'
#check Ideal.quotientMap_surjective
#check Ideal.Quotient.algebraMap_mk_of_liesOver
#check Int.quotientSpanNatEquivZMod
#check Ideal.quotEquivOfEq
#check Ideal.le_comap_map
#check Ideal.map_id

/-! ## 2. The S2587LocalizedResidueDataS form: (Z / (613)) ->+* (S / D.p) -/

/-- The only ingredient the S2587 datum supplies for Ideal.quotientMap: the
membership 613 in D.p turns into span{613} <= D.p.comap (algebraMap Z S).
No LiesOver instance is needed (and none is stored in S2587LocalizedResidueDataS). -/
theorem span613_le_comap_of_mem {D : S2587LocalizedResidueDataS}
    (h613 : algebraMap ℤ S (613 : ℤ) ∈ D.p) :
    Ideal.span {(613 : ℤ)} ≤ D.p.comap (algebraMap ℤ S) := by
  rw [Ideal.span_singleton_le_iff_mem]
  exact h613

/-- Concrete Ideal.quotientMap on the localized L side, from the S2587 datum:
R = Z, I = span{613}, T = S, J = D.p, f = algebraMap Z S. -/
noncomputable def residueMapZL (D : S2587LocalizedResidueDataS)
    (h613 : algebraMap ℤ S (613 : ℤ) ∈ D.p) :
    (ℤ ⧸ Ideal.span {(613 : ℤ)}) →+* (S ⧸ D.p) :=
  Ideal.quotientMap D.p (algebraMap ℤ S) (span613_le_comap_of_mem h613)

@[simp] theorem residueMapZL_mk (D : S2587LocalizedResidueDataS)
    (h613 : algebraMap ℤ S (613 : ℤ) ∈ D.p) (x : ℤ) :
    residueMapZL D h613 (Ideal.Quotient.mk (Ideal.span {(613 : ℤ)}) x) =
      Ideal.Quotient.mk D.p (algebraMap ℤ S x) := by
  simp only [residueMapZL, Ideal.quotientMap_mk]

/-- The same map with the source identified with ZMod 613. -/
noncomputable def residueMapZModL (D : S2587LocalizedResidueDataS)
    (h613 : algebraMap ℤ S (613 : ℤ) ∈ D.p) :
    ZMod 613 →+* (S ⧸ D.p) :=
  (residueMapZL D h613).comp (Int.quotientSpanNatEquivZMod 613).symm.toRingHom

/-! ## 3. The witness form at the chosen prime over 613: the O_L side -/

/-- O_L-side residue map at the chosen prime: R = Z, I = span{613}, T = C,
J = W.p, f = algebraMap Z C; the inclusion is W.p_liesOver. -/
noncomputable def residueMapZC (W : S2584PrimeDegreeOneWitness) :
    (ℤ ⧸ Ideal.span {(613 : ℤ)}) →+* (C ⧸ W.p) :=
  Ideal.quotientMap W.p (algebraMap ℤ C) (le_of_eq W.p_liesOver.over)

@[simp] theorem residueMapZC_mk (W : S2584PrimeDegreeOneWitness) (x : ℤ) :
    residueMapZC W (Ideal.Quotient.mk (Ideal.span {(613 : ℤ)}) x) =
      Ideal.Quotient.mk W.p (algebraMap ℤ C x) := by
  simp only [residueMapZC, Ideal.quotientMap_mk]

/-- The O_L-side residue map is injective: the ideal W.p lies over (613). -/
theorem residueMapZC_injective (W : S2584PrimeDegreeOneWitness) :
    Function.Injective (residueMapZC W) := by
  simp only [residueMapZC]
  exact Ideal.quotientMap_injective' (le_of_eq W.p_liesOver.over.symm)

/-- The O_L-side residue map with the source identified with ZMod 613. -/
noncomputable def residueMapZModC (W : S2584PrimeDegreeOneWitness) :
    ZMod 613 →+* (C ⧸ W.p) :=
  (residueMapZC W).comp (Int.quotientSpanNatEquivZMod 613).symm.toRingHom

/-! ## 4. The witness form: the localized prime W.P -/

/-- Localized residue map at the chosen prime: R = Z, I = span{613}, T = S,
J = W.P, f = algebraMap Z S. -/
noncomputable def residueMapZS (W : S2584PrimeDegreeOneWitness) :
    (ℤ ⧸ Ideal.span {(613 : ℤ)}) →+* (S ⧸ W.P) :=
  Ideal.quotientMap W.P (algebraMap ℤ S) (le_of_eq W.P_liesOver.over)

@[simp] theorem residueMapZS_mk (W : S2584PrimeDegreeOneWitness) (x : ℤ) :
    residueMapZS W (Ideal.Quotient.mk (Ideal.span {(613 : ℤ)}) x) =
      Ideal.Quotient.mk W.P (algebraMap ℤ S x) := by
  simp only [residueMapZS, Ideal.quotientMap_mk]

/-- The localization residue map C / W.p ->+* S / W.P at the chosen prime:
R = C, I = W.p, T = S, J = W.P, f = algebraMap C S, hIJ from W.P_liesOver_p. -/
noncomputable def residueMapCS (W : S2584PrimeDegreeOneWitness) :
    (C ⧸ W.p) →+* (S ⧸ W.P) :=
  Ideal.quotientMap W.P (algebraMap C S) (le_of_eq W.P_liesOver_p.over)

@[simp] theorem residueMapCS_mk (W : S2584PrimeDegreeOneWitness) (x : C) :
    residueMapCS W (Ideal.Quotient.mk W.p x) =
      Ideal.Quotient.mk W.P (algebraMap C S x) := by
  simp only [residueMapCS, Ideal.quotientMap_mk]

/-- The localization residue map is injective at the chosen prime. -/
theorem residueMapCS_injective (W : S2584PrimeDegreeOneWitness) :
    Function.Injective (residueMapCS W) := by
  simp only [residueMapCS]
  exact Ideal.quotientMap_injective' (le_of_eq W.P_liesOver_p.over.symm)

/-- The same localization map with the ideal W.p.map (algebraMap C S) in place of
W.P: hIJ = Ideal.le_comap_map, so no LiesOver hypothesis is needed. -/
noncomputable def residueMapCSmap (W : S2584PrimeDegreeOneWitness) :
    (C ⧸ W.p) →+* (S ⧸ W.p.map (algebraMap C S)) :=
  Ideal.quotientMap (W.p.map (algebraMap C S)) (algebraMap C S) Ideal.le_comap_map

@[simp] theorem residueMapCSmap_mk (W : S2584PrimeDegreeOneWitness) (x : C) :
    residueMapCSmap W (Ideal.Quotient.mk W.p x) =
      Ideal.Quotient.mk (W.p.map (algebraMap C S)) (algebraMap C S x) := by
  simp only [residueMapCSmap, Ideal.quotientMap_mk]

/-- The le_rfl parameter shape (the one used by
S2591LocalizedResidueEquivActual.S2591_localized_residue_equiv):
(C / W.P.comap (algebraMap C S)) ->+* (S / W.P). -/
noncomputable def residueMapLocalized (W : S2584PrimeDegreeOneWitness) :
    (C ⧸ W.P.comap (algebraMap C S)) →+* (S ⧸ W.P) :=
  Ideal.quotientMap W.P (algebraMap C S) le_rfl

/-! ## 5. Ideal.quotientEquiv and Ideal.Quotient.lift concretely -/

/- API gotcha found by this probe (recorded for reuse): the inclusion needed by
Ideal.quotientEquiv at the identity of C is
  W.P.comap (algebraMap C S) = W.p.map (↑(RingEquiv.refl C)),
and plain rw [Ideal.map_id] does not fire on it, because
↑(RingEquiv.refl C) : C →+* C is not syntactically RingHom.id C.  The first error was

  Tactic rewrite failed: Did not find an occurrence of the pattern
    Ideal.map (RingHom.id ?m) ?I
  in the target expression
    Ideal.comap (algebraMap C S) W.P = Ideal.map (↑(RingEquiv.refl C)) W.p

The fix is the explicit coercion lemma below. -/

/-- The C-side prime W.p and the contraction W.P.comap (algebraMap C S) are equal,
so Ideal.quotientEquiv transports quotients along the identity of C. -/
noncomputable def comapQuotEquiv (W : S2584PrimeDegreeOneWitness) :
    (C ⧸ W.p) ≃+* (C ⧸ W.P.comap (algebraMap C S)) :=
  Ideal.quotientEquiv W.p (W.P.comap (algebraMap C S)) (RingEquiv.refl C) (by
    have h : (↑(RingEquiv.refl C) : C →+* C) = RingHom.id C := rfl
    rw [h, Ideal.map_id]
    exact W.P_liesOver_p.over.symm)

/-- Ideal.Quotient.lift at the chosen prime: the witness residue equivalence
C / W.p ~= ZMod 613 is the lift of its composite with the quotient map. -/
noncomputable def residueLift (W : S2584PrimeDegreeOneWitness) :
    (C ⧸ W.p) →+* ZMod 613 :=
  Ideal.Quotient.lift (I := W.p)
    (W.residueEquiv.toRingHom.comp (Ideal.Quotient.mk W.p)) (by
      intro x hx
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero])

theorem residueLift_eq (W : S2584PrimeDegreeOneWitness) :
    residueLift W = W.residueEquiv.toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  simp [residueLift]

/-! ## 5b. The concrete quotientMap is the canonical residue algebraMap -/

/-- The O_L-side concrete quotientMap is *definitionally* the canonical residue
algebra map of Ideal.Quotient.algebraOfLiesOver, i.e. the map used by the
Kummer-Dedekind residue equivalence (S2579_quotient_equiv). -/
theorem residueMapZC_eq_algebraMap (W : S2584PrimeDegreeOneWitness)
    [W.p.LiesOver (Ideal.span {(613 : ℤ)})] :
    letI : Algebra (ℤ ⧸ Ideal.span {(613 : ℤ)}) (C ⧸ W.p) :=
      Ideal.Quotient.algebraOfLiesOver W.p (Ideal.span {(613 : ℤ)})
    residueMapZC W = algebraMap (ℤ ⧸ Ideal.span {(613 : ℤ)}) (C ⧸ W.p) := rfl

/-- The le_rfl localization map residueMapLocalized is definitionally the canonical
quotient algebra map of Ideal.Quotient.quotientAlgebra. -/
theorem residueMapLocalized_eq_algebraMap (W : S2584PrimeDegreeOneWitness) :
    residueMapLocalized W =
      algebraMap (C ⧸ W.P.comap (algebraMap C S)) (S ⧸ W.P) := rfl

/-! ## 6. The residue isomorphisms at the chosen prime -/

/-- The O_L-side residue isomorphism at the chosen prime over 613. -/
noncomputable def residueEquivC (W : S2584PrimeDegreeOneWitness) :
    (C ⧸ W.p) ≃+* ZMod 613 :=
  W.residueEquiv

/-- The localized residue isomorphism at the chosen prime over 613. -/
noncomputable def residueEquivS (W : S2584PrimeDegreeOneWitness) :
    (S ⧸ W.P) ≃+* ZMod 613 :=
  W.residueEquivS

/-- The quotient identification between the localized and unlocalized residue
rings at the chosen prime. -/
noncomputable def quotientEquivCS (W : S2584PrimeDegreeOneWitness) :
    (S ⧸ W.P) ≃+* (C ⧸ W.p) :=
  W.quotientEquiv

/-! ## 7. Types of the new declarations (for the record) -/

#check residueMapZL
#check residueMapZModL
#check residueMapZC
#check residueMapZModC
#check residueMapZS
#check residueMapCS
#check residueMapCSmap
#check residueMapLocalized
#check comapQuotEquiv
#check residueLift
#check residueEquivC
#check residueEquivS
#check quotientEquivCS

/-! ## 8. Axiom footprint -/

#print axioms span613_le_comap_of_mem
#print axioms residueMapZL_mk
#print axioms residueMapZC_mk
#print axioms residueMapZC_injective
#print axioms residueMapZS_mk
#print axioms residueMapCS_mk
#print axioms residueMapCS_injective
#print axioms residueMapCSmap_mk
#print axioms residueLift_eq
#print axioms residueMapZC_eq_algebraMap
#print axioms residueMapLocalized_eq_algebraMap

end LeanFormal.IUT.XiFPaper.S2591ResidueIsoProbeActual

end
