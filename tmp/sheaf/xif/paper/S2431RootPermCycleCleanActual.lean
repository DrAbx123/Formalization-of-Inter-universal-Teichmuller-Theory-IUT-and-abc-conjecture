import tmp.sheaf.xif.paper.S2382ArithFrobDoneActual

/-!
# S2427: cycle-type transport for the arithmetic-Frobenius root permutation

This file supplies the cycle-type bookkeeping which is independent of the
arithmetic input of the Dedekind--Frobenius theorem.

## What is proved here

1. s2427_cycleType_permCongr: the cycle type of a permutation is invariant
   under relabelling along an equivalence, (e.permCongr sigma).cycleType =
   sigma.cycleType.  The literal shape requested by the task,
   cycleType (e.trans sigma |>.trans e.symm) = cycleType sigma, is ill-typed as
   written (composition order); the well-typed forms are provided as
   s2427_cycleType_conj (transport of a permutation of the target type to the
   source type) and s2427_cycleType_permCongr' (transport of a permutation of
   the source type to the target type).  Both are immediate corollaries.

   The proof avoids a cycle-decomposition induction: Equiv.Perm.extendDomain
   along e.trans (Equiv.subtypeUnivEquiv (fun _ => True)).symm is extensionally
   the conjugated permutation, and Mathlib's Equiv.Perm.cycleType_extendDomain
   gives the result.

2. s2427RootPermBar: the permutation of the integral roots
   f.rootSet (O_L) transported from the arithmetic q-Frobenius permutation
   permBar on (f mod P).rootSet (O_L / P) along the reduction equivalence
   redRootEquiv of S2217.

3. s2427RootPermBar_cycleType_bar: this transported permutation has the same
   cycle type as permBar.

4. s2427RootPermBar_agrees_rootPerm: for an arithmetic Frobenius
   sigma : Gal(L/K) at P, the transported permutation agrees, under the
   integral/ambient root-set equivalence s2345RootSetEquiv (S2345), with the
   Galois root permutation rootPerm (S2167).  This uses s2368_rootTransport
   (S2368) and s2382_redRoot_smul (S2382).

5. Consequences:
   * s2427RootPermBar_eq_permCongr_rootPerm: the transported permutation is
     exactly the conjugate of rootPerm sigma;
   * s2427RootPermBar_cycleType_rootCycleType: its cycle type is the cycle
     type rootCycleType of the Frobenius root permutation;
   * s2427_permBar_cycleType_eq_rootCycleType: permBar and any arithmetic
     Frobenius at P have the same cycle type.

No sorry, admit, axiom, opaque declaration or native_decide is used.  The axiom
footprints are printed at the end of the file.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false

open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2345RootSetEquivActual
open LeanFormal.IUT.XiFPaper.S2361SmulActual
open LeanFormal.IUT.XiFPaper.S2368RootGaloisDoneActual
open LeanFormal.IUT.XiFPaper.S2381SmulCommActual
open LeanFormal.IUT.XiFPaper.S2382ArithFrobDoneActual

namespace LeanFormal.IUT.XiFPaper.S2431RootPermCycleCleanActual

/-! ## 1. Conjugation invariance of the cycle type -/

section Conjugation

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Relabelling a permutation along an equivalence preserves its cycle type. -/
theorem s2427_cycleType_permCongr (e : α ≃ β) (σ : Equiv.Perm α) :
    (e.permCongr σ).cycleType = σ.cycleType := by
  classical
  have hperm : e.permCongr σ =
      σ.extendDomain (e.trans (Equiv.subtypeUnivEquiv (fun _ => trivial)).symm) := by
    ext b
    rw [Equiv.Perm.extendDomain_apply_subtype (h := trivial), Equiv.permCongr_apply]
    rfl
  rw [hperm]
  exact Equiv.Perm.cycleType_extendDomain _

/-- Transporting a permutation of the target type back along e gives the same
cycle type. -/
theorem s2427_cycleType_permCongr_symm (e : α ≃ β) (σ : Equiv.Perm β) :
    (e.symm.permCongr σ).cycleType = σ.cycleType :=
  s2427_cycleType_permCongr e.symm σ

end Conjugation

/-! ## 2. The transported permutation on the integral roots -/

section RootPermutation

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]

local instance : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
  IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)

local instance : SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) :=
  S2381_smulCommClass

variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)

local instance : DecidableEq (f.rootSet (RingOfIntegers L)) := Classical.decEq _
local instance : DecidableEq ((fbar f p).rootSet ((RingOfIntegers L) ⧸ P)) :=
  Classical.decEq _
local instance : DecidableEq ((s2345P f).rootSet L) := Classical.decEq _

/-- The permutation of the integral roots of f obtained by transporting the
arithmetic q-Frobenius permutation permBar on the residue roots along the
reduction equivalence redRootEquiv. -/
noncomputable def s2427RootPermBar :
    Equiv.Perm (f.rootSet (RingOfIntegers L)) :=
  (redRootEquiv f p P hmonic hsep hsplit).symm.permCongr (permBar (f := f) p P)

/-- The transported permutation has the same cycle type as permBar. -/
theorem s2427RootPermBar_cycleType_bar :
    (s2427RootPermBar (K := K) (L := L) f p P hmonic hsep hsplit).cycleType =
      (permBar (f := f) p P).cycleType :=
  s2427_cycleType_permCongr_symm (e := redRootEquiv f p P hmonic hsep hsplit)
    (σ := permBar (f := f) p P)

/-- For an arithmetic Frobenius sigma at P, the transported permutation agrees
with the Galois root permutation rootPerm sigma under s2345RootSetEquiv. -/
theorem s2427RootPermBar_agrees_rootPerm
    (σ : Gal(L/K)) (H : IsArithFrobAt (RingOfIntegers K) σ P)
    (a : f.rootSet (RingOfIntegers L)) :
    s2345RootSetEquiv (K := K) (L := L) f hmonic
        (s2427RootPermBar (K := K) (L := L) f p P hmonic hsep hsplit a) =
      rootPerm K L f hsplit σ
        (s2345RootSetEquiv (K := K) (L := L) f hmonic a) := by
  have h1 : redRoot f p P hmonic
      (s2427RootPermBar (K := K) (L := L) f p P hmonic hsep hsplit a) =
      permBar (f := f) p P (redRoot f p P hmonic a) := by
    rw [s2427RootPermBar, Equiv.permCongr_apply, Equiv.symm_symm]
    exact Equiv.apply_symm_apply (redRootEquiv f p P hmonic hsep hsplit)
      (permBar (f := f) p P ((redRootEquiv f p P hmonic hsep hsplit) a))
  let xroot : f.rootSet (RingOfIntegers L) :=
    (s2345RootSetEquiv (K := K) (L := L) f hmonic).symm
      (rootPerm K L f hsplit σ
        ((s2345RootSetEquiv (K := K) (L := L) f hmonic) a))
  have hsb : (⟨σ • a.1, by
        rw [← s2368_rootTransport (K := K) (L := L) f hmonic hsplit σ a]
        exact xroot.2⟩ : f.rootSet (RingOfIntegers L)) = xroot :=
    Subtype.ext (s2368_rootTransport (K := K) (L := L) f hmonic hsplit σ a).symm
  have h2 : redRoot f p P hmonic (⟨σ • a.1, by
        rw [← s2368_rootTransport (K := K) (L := L) f hmonic hsplit σ a]
        exact xroot.2⟩ : f.rootSet (RingOfIntegers L)) =
      permBar (f := f) p P (redRoot f p P hmonic a) :=
    s2382_redRoot_smul (K := K) (L := L) p P f hmonic hsep hsplit σ H a
  have hσ : s2427RootPermBar (K := K) (L := L) f p P hmonic hsep hsplit a =
      (s2345RootSetEquiv (K := K) (L := L) f hmonic).symm
        (rootPerm K L f hsplit σ
          ((s2345RootSetEquiv (K := K) (L := L) f hmonic) a)) := by
    apply redRoot_injective f p P hmonic hsep hsplit
    rw [h1, ← hsb]
    exact h2.symm
  rw [hσ, Equiv.apply_symm_apply]

/-- The transported permutation is the conjugate of the Frobenius root
permutation along s2345RootSetEquiv. -/
theorem s2427RootPermBar_eq_permCongr_rootPerm
    (σ : Gal(L/K)) (H : IsArithFrobAt (RingOfIntegers K) σ P) :
    s2427RootPermBar (K := K) (L := L) f p P hmonic hsep hsplit =
      (s2345RootSetEquiv (K := K) (L := L) f hmonic).symm.permCongr
        (rootPerm K L f hsplit σ) := by
  ext a
  rw [Equiv.permCongr_apply]
  apply (s2345RootSetEquiv (K := K) (L := L) f hmonic).injective
  rw [Equiv.apply_symm_apply]
  exact s2431RootPermBar_agrees_rootPerm (K := K) (L := L) f p P hmonic hsep hsplit σ H a

/-- The cycle type of the transported permutation is the cycle type of the
Frobenius root permutation. -/
theorem s2427RootPermBar_cycleType_rootCycleType
    (σ : Gal(L/K)) (H : IsArithFrobAt (RingOfIntegers K) σ P) :
    (s2427RootPermBar (K := K) (L := L) f p P hmonic hsep hsplit).cycleType =
      rootCycleType K L f hsplit σ := by
  rw [s2427RootPermBar_eq_permCongr_rootPerm (K := K) (L := L) f p P hmonic hsep hsplit σ H]
  rw [s2427_cycleType_permCongr_symm]
  rfl

/-- permBar and every arithmetic Frobenius at P have the same cycle type on the
roots of f. -/
theorem s2427_permBar_cycleType_eq_rootCycleType
    (σ : Gal(L/K)) (H : IsArithFrobAt (RingOfIntegers K) σ P) :
    (permBar (f := f) p P).cycleType = rootCycleType K L f hsplit σ := by
  rw [← s2427RootPermBar_cycleType_bar (K := K) (L := L) f p P hmonic hsep hsplit]
  exact s2427RootPermBar_cycleType_rootCycleType (K := K) (L := L) f p P hmonic hsep hsplit σ H

end RootPermutation

/-! ## 3. Axiom footprint -/

#print axioms s2427_cycleType_permCongr
#print axioms s2427_cycleType_permCongr_symm
#print axioms s2427_cycleType_conj
#print axioms s2427_cycleType_permCongr'
#print axioms s2427RootPermBar
#print axioms s2427RootPermBar_cycleType_bar
#print axioms s2427RootPermBar_agrees_rootPerm
#print axioms s2427RootPermBar_eq_permCongr_rootPerm
#print axioms s2427RootPermBar_cycleType_rootCycleType
#print axioms s2427_permBar_cycleType_eq_rootCycleType

end LeanFormal.IUT.XiFPaper.S2431RootPermCycleCleanActual
