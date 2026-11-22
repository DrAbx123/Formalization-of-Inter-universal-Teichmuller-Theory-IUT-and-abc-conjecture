 /-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S2566AdjoinIntegralCActual
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# A3: finite etale over a DVR => integrally closed (DVR-local route)

Context (actual files, all imported from S2566):

* R = Z[1/c], c = S2562HZcMonicCActual.Cden (S2565.R);
* L = S1720Field = SplittingField S1720H;
* HZc2 is monic over R and discr HZc2 is a unit in R (S2562, S2564);
* Aoc2 = Algebra.adjoin R (HZc2.rootSet L) (S2566);
* S = Localization (algebraMapSubmonoid C (powers c)), and
  IsIntegralClosure S R L (S2565);
* Aoc2 is a subset of S (S2566).

This file proves, with no sorry, no native_decide and no new axiom:

1. R is a Dedekind domain and is not a field (the prime 11 does not divide
   Cden: Cden = 1 (mod 11)), hence every maximal ideal p of R is nonzero.
2. For every maximal ideal p of R, the localization R_p = Localization.AtPrime p
   is a discrete valuation ring (rp_isDVR).
3. Aoc2 is finite over R (Aoc2_finite).
4. For every maximal p, R_p ⊗[R] Aoc2 is finite over R_p and, assuming
   Algebra.Etale R Aoc2, finite etale over R_p
   (Aoc2_tensor_Rp_finite, Aoc2_tensor_Rp_etale).
5. The exact missing Mathlib statement "finite etale over a DVR is integrally
   closed" is isolated as the proposition FiniteEtaleOverDVRIntegrallyClosed
   (not an axiom, no instance). Under this proposition and
   Algebra.Etale R Aoc2, the actual base change Aoc2 ⊗[R] R_p is integrally
   closed (Aoc2_tensor_Rp_isIntegrallyClosed).

The two precise gaps are documented at the end of the file.

## References

* Mathlib: IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain,
  IsLocalization.isDedekindDomain, Algebra.Etale.baseChange,
  Module.Finite.base_change.
-/

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial
open scoped TensorProduct

namespace LeanFormal.IUT.XiFPaper.A3DVRIntegrallyClosedAgent

open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2566AdjoinIntegralCActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual

/-! ## 1. R = Z[1/Cden] is a Dedekind domain and is not a field -/

lemma hc_mem' : (c : ℤ) ∈ nonZeroDivisors ℤ :=
  mem_nonZeroDivisors_of_ne_zero (by simpa using hcA)

/-- R = Z[1/c] is a Dedekind domain (localization of Z at a nonzero element). -/
theorem R_dedekind : IsDedekindDomain R := by
  haveI hdom : IsDomain R :=
    IsLocalization.isDomain_localization (M := Submonoid.powers c)
      (Submonoid.powers_le.mpr hc_mem')
  exact IsLocalization.isDedekindDomain (A := ℤ) (M := Submonoid.powers c)
    (Submonoid.powers_le.mpr hc_mem') R

/-- Instance form of R_dedekind; this is a proved instance, not an axiom. -/
instance R_dedekind_inst : IsDedekindDomain R := R_dedekind

theorem R_nontrivial : Nontrivial R := by
  refine ⟨0, 1, ?_⟩
  intro hh
  have h' : algebraMap ℤ R (0 : ℤ) = algebraMap ℤ R (1 : ℤ) := hh
  have hz : (0 : ℤ) = 1 :=
    IsLocalization.injective R (M := Submonoid.powers c)
      (Submonoid.powers_le.mpr hc_mem') h'
  norm_num at hz

/-- A small prime not dividing Cden; Cden = 2^34 * 3^3 * Dval and Dval = 4 (mod 11). -/
def q : ℕ := 11

instance : Fact q.Prime := ⟨by decide⟩

lemma c_mod_q : ((c : ℤ) : ZMod q) ≠ 0 := by
  unfold q c Cden c0 Dval
  decide

/-- c becomes a unit in ZMod q, hence the localization map Z -> Z[1/c]
extends to a ring homomorphism R -> ZMod q. -/
theorem hg : ∀ y : Submonoid.powers (c : ℤ),
    IsUnit ((Int.castRingHom (ZMod q)) (y : ℤ)) := by
  intro y
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (y : ℤ) c).mp y.2
  rw [← hn, map_pow]
  refine IsUnit.pow n ?_
  rw [isUnit_iff_ne_zero]
  simpa using c_mod_q

noncomputable def h : R →+* ZMod q :=
  IsLocalization.lift (M := Submonoid.powers (c : ℤ)) (g := Int.castRingHom (ZMod q)) hg

lemma h_apply (x : ℤ) : h (algebraMap ℤ R x) = (x : ZMod q) :=
  IsLocalization.lift_eq hg x

/-- R = Z[1/Cden] is not a field: 11 is a nonzero nonunit (h sends it to 0). -/
theorem R_not_isField : ¬ IsField R := by
  intro hf
  letI := hf.toField
  have hne : algebraMap ℤ R 11 ≠ 0 := by
    intro h0
    have hz : (11 : ℤ) = 0 := IsLocalization.injective R
      (M := Submonoid.powers c) (Submonoid.powers_le.mpr hc_mem') (by simpa using h0)
    norm_num at hz
  have hunit : IsUnit (algebraMap ℤ R 11) := isUnit_iff_ne_zero.mpr hne
  have hunit0 : IsUnit (h (algebraMap ℤ R 11)) := hunit.map h
  have hzero : h (algebraMap ℤ R 11) = 0 := by rw [h_apply]; decide
  rw [hzero] at hunit0
  exact not_isUnit_zero hunit0

/-- **Every maximal localization of R is a DVR.** The statement carries the
IsPrime/IsDomain instances needed by the IsDiscreteValuationRing class. -/
theorem rp_isDVR (p : Ideal R) [hp : p.IsMaximal] :
    letI : p.IsPrime := hp.isPrime
    letI : IsDomain (Localization.AtPrime p) :=
      IsLocalization.isDomain_of_local_atPrime (P := p) hp.isPrime
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  haveI : IsDedekindDomain R := R_dedekind
  haveI : p.IsPrime := hp.isPrime
  haveI : IsDomain (Localization.AtPrime p) :=
    IsLocalization.isDomain_of_local_atPrime (P := p) hp.isPrime
  have hp0 : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp R_not_isField
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hp0 _

/-! ## 2. Aoc2 is finite over R, and its base change to R_p -/

/-- S2566.Aoc2 is defined using HZc2 : R2[X]; the R-algebra and R2-algebra
structures on L agree by definition. -/
local instance : Algebra R2 L := inferInstanceAs (Algebra R L)

/-- Aoc2 = R[HZc2.rootSet L] is finite over R. -/
theorem Aoc2_finite : Module.Finite R Aoc2 := by
  haveI : Algebra.IsIntegral R Aoc2 :=
    Algebra.IsIntegral.adjoin (fun x hx => HZc2_root_isIntegral hx)
  haveI : Algebra.FiniteType R Aoc2 :=
    Algebra.FiniteType.adjoin_of_finite (Polynomial.rootSet_finite HZc2 L)
  exact Algebra.IsIntegral.finite

/-- Base change of the finiteness of Aoc2 to R_p (in the orientation
R_p ⊗[R] Aoc2 used by Algebra.Etale.baseChange). -/
theorem Aoc2_tensor_Rp_finite (p : Ideal R) [p.IsMaximal] :
    Module.Finite (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] Aoc2) := by
  haveI : Module.Finite R Aoc2 := Aoc2_finite
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] Aoc2) :=
    Algebra.TensorProduct.leftAlgebra
  exact Module.Finite.base_change (R := R) (A := Localization.AtPrime p) (M := Aoc2)

/-- If Aoc2 is etale over R, then its base change to R_p is etale over R_p.
(The hypothesis Algebra.Etale R Aoc2 is the second missing input; see the end
of the file.) -/
theorem Aoc2_tensor_Rp_etale (p : Ideal R) [p.IsMaximal] (het : Algebra.Etale R Aoc2) :
    Algebra.Etale (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] Aoc2) := by
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] Aoc2) :=
    Algebra.TensorProduct.leftAlgebra
  exact Algebra.Etale.baseChange R Aoc2 (Localization.AtPrime p)

/-! ## 3. The missing Mathlib theorem and its consequence -/

/-- **The exact missing statement**: a finite etale algebra over a discrete
valuation ring is integrally closed.

Mathlib v4.32.2 has no instance or theorem of this form (searched:
Mathlib/RingTheory/Etale, Unramified, DedekindDomain, LocalProperties).
The statement is therefore recorded as a proposition, not as an axiom and not
as an instance. Its intended Mathlib name is
Algebra.Etale.isIntegrallyClosed_of_isDiscreteValuationRing. -/
def FiniteEtaleOverDVRIntegrallyClosed : Prop :=
  ∀ (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [Algebra.Etale A B],
    IsIntegrallyClosed B

/-- **Conditional DVR-local consequence.** Under the missing theorem and the
missing finite-etaleness of Aoc2, the actual algebra Aoc2 ⊗[R] R_p is
integrally closed for every maximal ideal p of R.

The proof applies the gap statement to R_p ⊗[R] Aoc2 (the orientation for
which the base-change instances are stated) and transports integrally closedness
along TensorProduct.comm. -/
theorem Aoc2_tensor_Rp_isIntegrallyClosed
    (hgap : FiniteEtaleOverDVRIntegrallyClosed)
    (het : Algebra.Etale R Aoc2)
    (p : Ideal R) [hp : p.IsMaximal] :
    IsIntegrallyClosed (Aoc2 ⊗[R] Localization.AtPrime p) := by
  haveI : IsDedekindDomain R := R_dedekind
  haveI : p.IsPrime := hp.isPrime
  haveI : IsDomain (Localization.AtPrime p) :=
    IsLocalization.isDomain_of_local_atPrime (P := p) hp.isPrime
  haveI : IsDiscreteValuationRing (Localization.AtPrime p) := rp_isDVR p
  haveI : Module.Finite R Aoc2 := Aoc2_finite
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] Aoc2) :=
    Algebra.TensorProduct.leftAlgebra
  haveI : Module.Finite (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] Aoc2) :=
    Module.Finite.base_change (R := R) (A := Localization.AtPrime p) (M := Aoc2)
  haveI : Algebra.Etale (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] Aoc2) :=
    Algebra.Etale.baseChange R Aoc2 (Localization.AtPrime p)
  have h : IsIntegrallyClosed (Localization.AtPrime p ⊗[R] (Aoc2 : Type)) :=
    hgap (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] (Aoc2 : Type))
  exact IsIntegrallyClosed.of_equiv
    (Algebra.TensorProduct.comm R (Localization.AtPrime p) Aoc2).symm.toRingEquiv

/-! ## 4. Exact remaining gaps and required API

### Gap G1: finite etale over a DVR => integrally closed

The proposition FiniteEtaleOverDVRIntegrallyClosed above is not proved.
The needed Mathlib API is one of:

* a theorem Algebra.Etale.isIntegrallyClosed_of_isDiscreteValuationRing
  (the statement of the proposition), or
* a theorem that a finite etale A-algebra over a DVR is a finite product of
  DVRs (Algebra.Etale.exists_algEquiv_pi_isDiscreteValuationRing), together
  with IsIntegrallyClosed of a finite product of integrally closed rings, or
* the following primitive ingredients, which are not currently packaged:
  1. Module.Flat A B from Algebra.Smooth.flat (available);
  2. IsFractionRing B (B ⊗[A] FractionRing A) for finite flat B over a DVR
     A (not available; the proof needs that nonzero divisors of B become
     units in the finite Artinian algebra B ⊗[A] FractionRing A, using
     IsArtinianRing.isUnit_of_mem_nonZeroDivisors (available) and the
     reducedness of B ⊗[A] FractionRing A over a field (available via
     Algebra.FormallyUnramified.isReduced_of_field));
  3. reducedness of B modulo a uniformizer pi, together with the element
     argument: write x = b / pi^n, clear denominators in IsIntegral A x, and
     use (b mod pi)^n = 0 to descend n.
     The base-change identification
     B/(pi) is isomorphic to (A/(pi)) ⊗[A] B
     is available as Algebra.TensorProduct.quotIdealMapEquivQuotTensor,
     but the Algebra.Etale/IsReduced instance for the quotient is not.

### Gap G2: Algebra.Etale R Aoc2

Aoc2 is the R-subalgebra generated by the whole root set of HZc2.
Mathlib has:

* StandardEtalePair and Algebra.Etale.of_isLocalizationAway for a single
  root R[X]/(f) when f is monic and separable (derivative invertible);
* no theorem that the compositum/splitting algebra generated by all roots of
  a monic separable polynomial is finite etale.

The exact missing lemma is:

  Polynomial.Separable.isFiniteEtale_adjoin_rootSet:
  for f : R[X] monic with IsUnit (discr f) (or f.Separable),
  Algebra.Etale R (Algebra.adjoin R (f.rootSet L)) for any R-algebra L
  in which f splits,

or, alternatively, an identification Aoc2 = S with S the integral closure,
which is exactly the reverse inclusion S2568 would provide after
IsIntegrallyClosed Aoc2 is known.

At present het : Algebra.Etale R Aoc2 is therefore an explicit hypothesis.
-/

#print axioms R_dedekind
#print axioms R_not_isField
#print axioms rp_isDVR
#print axioms Aoc2_finite
#print axioms Aoc2_tensor_Rp_finite
#print axioms Aoc2_tensor_Rp_etale
#print axioms Aoc2_tensor_Rp_isIntegrallyClosed

end LeanFormal.IUT.XiFPaper.A3DVRIntegrallyClosedAgent
