/-
S2598c: the cycle type of the concrete localized permBar is {12}.

Setup (S2548 / S2667): f = f10' (S2577), p = p10 (S2577), and
P = P10 W (S2663) for a degree-one witness W.  This file feeds the
actual S2598b hypotheses (hmonic, hsep, hsplit) into
S2548ConcreteCycleTypeActual.concrete_permBar_cycleType and evaluates
factorDegrees with fbar10_irreducible + fbar10_natDegree.

## The witness parameter

The literal statement requested by the parent,

  (permBar (f := f10') (p := p10) (P := P10 W)).cycleType = {12}

for an *arbitrary* W : S2584PrimeDegreeOneWitness, is not a well-formed
proposition: permBar has the instance argument [P.LiesOver p], and P10 W
lies over S2661P10Actual.p10 W, not over S2577Away10FbarActual.p10 (the
latter is ker phi10, attached to the canonical choice
S2577Away10FbarActual.W).  For W = S2577Away10FbarActual.W the needed
instance is S2581S2543ParamsActual.P10_lies_p10_self, which we register
below.  For a general W, the needed instance is exactly the hypothesis
hPover of S2598c_permBar_cycleType_12_of_liesOver; it is false for
witnesses whose prime W.p differs from the canonical one (the twelve
distinct roots of P12 mod 613 give twelve distinct such primes).
Hence we prove:

* S2598c_permBar_cycleType_12_of_liesOver : the requested statement for a
  general W, with the missing instance (P10 W).LiesOver p10 as a
  hypothesis;
* S2598c_permBar_cycleType_12 : the unconditional concrete statement for
  the canonical witness S2577Away10FbarActual.W, which is the actual
  localized target (p = S2577.p10, P = P10 W).

No sorry, axiom, native_decide or True is used.
-/
import tmp.sheaf.xif.paper.S2598bHsepSplitActual
import tmp.sheaf.xif.paper.S2663P10PrimeActual
import tmp.sheaf.xif.paper.S2664P10MaxActual
import tmp.sheaf.xif.paper.S2665P10FintypeActual
import tmp.sheaf.xif.paper.S2581S2543ParamsActual
import tmp.sheaf.xif.paper.S2548ConcreteCycleTypeActual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial NumberField

namespace LeanFormal.IUT.XiFPaper.S2598cPermBar12Actual

open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2577Away10FbarActual
open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2663P10PrimeActual
open LeanFormal.IUT.XiFPaper.S2664P10MaxActual
open LeanFormal.IUT.XiFPaper.S2665P10FintypeActual
open LeanFormal.IUT.XiFPaper.S2581S2543ParamsActual
open LeanFormal.IUT.XiFPaper.S2548ConcreteCycleTypeActual
open LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual

abbrev R10 : Type := S2537ConcreteLocalizationActual.R
abbrev T10 : Type := S2537ConcreteLocalizationActual.S

/-! ## 1. Instances needed to state permBar at (p10, P10 W) -/

attribute [local instance] S2577Away10FbarActual.p10_max

attribute [local instance] S2663P10PrimeActual.P10_prime

attribute [local instance] S2664P10MaxActual.P10_isMaximal

attribute [local instance] S2581S2543ParamsActual.P10_lies_p10_self

/-- Decidable equality on the residue field T10 / P10 W. -/
noncomputable instance instDecidableEqQuotP10 (W : S2584PrimeDegreeOneWitness) :
    DecidableEq (T10 ⧸ S2663P10PrimeActual.P10 W) :=
  Classical.decEq _

/-! ## 2. Monic-ness of the reduced polynomial -/

/-- fbar10 = f10' mod p10 is monic. -/
theorem fbar10_monic : S2577Away10FbarActual.fbar10.Monic :=
  S2598bHsepSplitActual.S2598b_hmonic.map
    (Ideal.Quotient.mk S2577Away10FbarActual.p10)

/-! ## 3. Factor degrees of a monic irreducible of degree twelve -/

/-- The corrected factor-degree multiset of a monic irreducible polynomial of
degree twelve is {12}. -/
theorem factorDegrees_filter_irreducible {k : Type} [Field k] {g : k[X]}
    (hg : g.Monic) (hirr : Irreducible g) (hdeg : g.natDegree = 12) :
    (LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual.factorDegrees g).filter
        (fun n => n ≠ 1) = ({12} : Multiset Nat) := by
  classical
  letI : DecidableEq k := Classical.decEq k
  unfold LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual.factorDegrees
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hirr,
    Monic.normalize_eq_self hg]
  simp [hdeg]

/-! ## 4. The concrete cycle-type computation -/

/-- Conditional form for a general witness: if P10 W lies over the canonical
p10, then the concrete permBar has cycle type {12}. -/
theorem S2598c_permBar_cycleType_12_of_liesOver (W : S2584PrimeDegreeOneWitness)
    [hPover : (S2663P10PrimeActual.P10 W).LiesOver S2577Away10FbarActual.p10] :
    (permBar (f := S2577Away10FbarActual.f10')
      (p := S2577Away10FbarActual.p10)
      (P := S2663P10PrimeActual.P10 W)).cycleType = ({12} : Multiset Nat) := by
  classical
  letI : Field (R10 ⧸ S2577Away10FbarActual.p10) :=
    Ideal.Quotient.field S2577Away10FbarActual.p10
  have hcyc :=
    LeanFormal.IUT.XiFPaper.S2548ConcreteCycleTypeActual.concrete_permBar_cycleType
      (f := S2577Away10FbarActual.f10')
      (p := S2577Away10FbarActual.p10)
      (P := S2663P10PrimeActual.P10 W)
      (hmonic := S2598bHsepSplitActual.S2598b_hmonic)
      (hsep := S2598bHsepSplitActual.S2598b_hsep)
      (hsplit := S2598bHsepSplitActual.S2598b_hsplit)
  rw [hcyc]
  exact factorDegrees_filter_irreducible fbar10_monic
    S2577Away10FbarActual.fbar10_irreducible
    S2577Away10FbarActual.fbar10_natDegree

/-- The concrete localized target: for the canonical witness
S2577Away10FbarActual.W, the permBar attached to (f10', p10, P10 W) has
cycle type {12}. -/
theorem S2598c_permBar_cycleType_12 :
    (permBar (f := S2577Away10FbarActual.f10')
      (p := S2577Away10FbarActual.p10)
      (P := S2663P10PrimeActual.P10 S2577Away10FbarActual.W)).cycleType =
      ({12} : Multiset Nat) :=
  S2598c_permBar_cycleType_12_of_liesOver S2577Away10FbarActual.W

/-! ## 5. Axiom footprint -/

#check S2598c_permBar_cycleType_12
#check S2598c_permBar_cycleType_12_of_liesOver
#check fbar10_monic
#check factorDegrees_filter_irreducible
#print axioms S2598c_permBar_cycleType_12
#print axioms S2598c_permBar_cycleType_12_of_liesOver
#print axioms fbar10_monic
#print axioms factorDegrees_filter_irreducible

end LeanFormal.IUT.XiFPaper.S2598cPermBar12Actual
end