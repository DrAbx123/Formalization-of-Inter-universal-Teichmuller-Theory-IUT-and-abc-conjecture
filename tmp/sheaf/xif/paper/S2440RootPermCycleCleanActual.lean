import tmp.sheaf.xif.paper.S2382ArithFrobDoneActual
noncomputable section
set_option maxHeartbeats 4000000
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2345RootSetEquivActual
open LeanFormal.IUT.XiFPaper.S2368RootGaloisDoneActual
open LeanFormal.IUT.XiFPaper.S2382ArithFrobDoneActual
namespace LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
local instance : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
  IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)
local instance : SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) :=
  LeanFormal.IUT.XiFPaper.S2381SmulCommActual.S2381_smulCommClass
variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
local instance : DecidableEq (f.rootSet (RingOfIntegers L)) := Classical.decEq _
local instance : DecidableEq ((fbar f p).rootSet ((RingOfIntegers L) ⧸ P)) := Classical.decEq _
local instance : DecidableEq ((f.map (algebraMap (RingOfIntegers K) K)).rootSet L) := Classical.decEq _
/-- S2345 equivalence with codomain definitionally the rootSet of f over K. -/
noncomputable def s2440RootSetEquiv :
    f.rootSet (RingOfIntegers L) ≃
      (f.map (algebraMap (RingOfIntegers K) K)).rootSet L :=
  s2345RootSetEquiv (K := K) (L := L) f hmonic
@[simp]
theorem s2440RootSetEquiv_apply (a : f.rootSet (RingOfIntegers L)) :
    ((s2440RootSetEquiv (K := K) (L := L) f hmonic a).1 : L) =
      algebraMap (RingOfIntegers L) L a.1 := rfl
section Conj
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
theorem s2440_cycleType_permCongr (e : α ≃ β) (σ : Equiv.Perm α) :
    (e.permCongr σ).cycleType = σ.cycleType := by
  classical
  have hperm : e.permCongr σ =
      σ.extendDomain (e.trans (Equiv.subtypeUnivEquiv (fun _ => trivial)).symm) := by
    ext b
    rw [Equiv.Perm.extendDomain_apply_subtype (h := trivial), Equiv.permCongr_apply]
    rfl
  rw [hperm]
  exact Equiv.Perm.cycleType_extendDomain _
end Conj

/-- The integral-root permutation transported from permBar. -/
noncomputable def s2440RootPermBar : Equiv.Perm (f.rootSet (RingOfIntegers L)) :=
  (redRootEquiv f p P hmonic hsep hsplit).symm.permCongr (permBar (f := f) p P)
theorem s2440RootPermBar_cycleType :
    (s2440RootPermBar (K := K) (L := L) f p P hmonic hsep hsplit).cycleType =
      (permBar (f := f) p P).cycleType := by
  have h := Equiv.permCongr (redRootEquiv f p P hmonic hsep hsplit).symm
    (permBar (f := f) p P)
  -- cycle type invariant under permCongr
  simpa [s2440RootPermBar] using s2440_cycleType_permCongr (e := (redRootEquiv f p P hmonic hsep hsplit).symm) (σ := permBar (f := f) p P)

theorem s2440RootPermBar_agrees_rootPerm
    (σ : Gal(L/K)) (H : IsArithFrobAt (RingOfIntegers K) σ P)
    (a : f.rootSet (RingOfIntegers L)) :
    s2440RootSetEquiv (K := K) (L := L) f hmonic
        (s2440RootPermBar (K := K) (L := L) f p P hmonic hsep hsplit a) =
      rootPerm K L f hsplit σ
        (s2440RootSetEquiv (K := K) (L := L) f hmonic a) := by
  have h1 : redRoot f p P hmonic
      (s2440RootPermBar (K := K) (L := L) f p P hmonic hsep hsplit a) =
      permBar (f := f) p P (redRoot f p P hmonic a) := by
    rw [s2440RootPermBar, Equiv.permCongr_apply, Equiv.symm_symm]
    exact Equiv.apply_symm_apply (redRootEquiv f p P hmonic hsep hsplit)
      (permBar (f := f) p P ((redRootEquiv f p P hmonic hsep hsplit) a))
  let xroot : f.rootSet (RingOfIntegers L) :=
    (s2440RootSetEquiv (K := K) (L := L) f hmonic).symm
      (rootPerm K L f hsplit σ
        ((s2440RootSetEquiv (K := K) (L := L) f hmonic) a))
  have hsb : (⟨σ • a.1, by
        rw [← s2368_rootTransport (K := K) (L := L) f hmonic hsplit σ a]
        exact xroot.2⟩ : f.rootSet (RingOfIntegers L)) = xroot :=
    Subtype.ext (s2368_rootTransport (K := K) (L := L) f hmonic hsplit σ a).symm
  have h2 : redRoot f p P hmonic (⟨σ • a.1, by
        rw [← s2368_rootTransport (K := K) (L := L) f hmonic hsplit σ a]
        exact xroot.2⟩ : f.rootSet (RingOfIntegers L)) =
      permBar (f := f) p P (redRoot f p P hmonic a) :=
    s2382_redRoot_smul (K := K) (L := L) p P f hmonic hsep hsplit σ H a
  have hred : redRoot f p P hmonic
      (s2440RootPermBar (K := K) (L := L) f p P hmonic hsep hsplit a) =
      redRoot f p P hmonic xroot := by
    rw [h1, ← hsb, h2]
  have heq : s2440RootPermBar (K := K) (L := L) f p P hmonic hsep hsplit a = xroot :=
    redRoot_injective f p P hmonic hsep hsplit hred
  rw [heq]
  simp [xroot]

theorem s2440RootPermBar_eq_permCongr_rootPerm
    (σ : Gal(L/K)) (H : IsArithFrobAt (RingOfIntegers K) σ P) :
    s2440RootPermBar (K := K) (L := L) f p P hmonic hsep hsplit =
      (s2440RootSetEquiv (K := K) (L := L) f hmonic).symm.permCongr
        (rootPerm K L f hsplit σ) := by
  ext a
  rw [Equiv.permCongr_apply, Equiv.symm_symm]
  have h := congrArg (fun z : (f.map (algebraMap (RingOfIntegers K) K)).rootSet L => (z.1 : L))
      (s2440RootPermBar_agrees_rootPerm (K := K) (L := L) f p P hmonic hsep hsplit σ H a)
  change algebraMap (RingOfIntegers L) L
      (s2440RootPermBar (K := K) (L := L) f p P hmonic hsep hsplit a).1 =
    algebraMap (RingOfIntegers L) L
      ((s2440RootSetEquiv (K := K) (L := L) f hmonic).symm
        (rootPerm K L f hsplit σ
          ((s2440RootSetEquiv (K := K) (L := L) f hmonic) a))).1
  rw [← s2440RootSetEquiv_apply (K := K) (L := L) f hmonic
    (a := s2440RootPermBar (K := K) (L := L) f p P hmonic hsep hsplit a)]
  rw [show algebraMap (RingOfIntegers L) L
      ((s2440RootSetEquiv (K := K) (L := L) f hmonic).symm
        (rootPerm K L f hsplit σ
          ((s2440RootSetEquiv (K := K) (L := L) f hmonic) a))).1 =
      ((s2440RootSetEquiv (K := K) (L := L) f hmonic)
        ((s2440RootSetEquiv (K := K) (L := L) f hmonic).symm
          (rootPerm K L f hsplit σ
            ((s2440RootSetEquiv (K := K) (L := L) f hmonic) a)))).1 from
      (s2440RootSetEquiv_apply (K := K) (L := L) f hmonic
        (a := (s2440RootSetEquiv (K := K) (L := L) f hmonic).symm
          (rootPerm K L f hsplit σ
            ((s2440RootSetEquiv (K := K) (L := L) f hmonic) a)))).symm]
  rw [Equiv.apply_symm_apply]
  exact h

theorem s2440RootPermBar_cycleType_rootCycleType
    (σ : Gal(L/K)) (H : IsArithFrobAt (RingOfIntegers K) σ P) :
    (s2440RootPermBar (K := K) (L := L) f p P hmonic hsep hsplit).cycleType =
      rootCycleType K L f hsplit σ := by
  rw [s2440RootPermBar_eq_permCongr_rootPerm (K := K) (L := L) f p P hmonic hsep hsplit σ H]
  rw [s2440_cycleType_permCongr]
  rfl

theorem s2440_permBar_cycleType_eq_rootCycleType
    (hmonic : f.Monic) (hsep : (fbar f p).Separable)
    (σ : Gal(L/K)) (H : IsArithFrobAt (RingOfIntegers K) σ P) :
    (permBar (f := f) p P).cycleType = rootCycleType K L f hsplit σ := by
  rw [← s2440RootPermBar_cycleType (K := K) (L := L) f p P hmonic hsep hsplit]
  exact s2440RootPermBar_cycleType_rootCycleType (K := K) (L := L) f p P hmonic hsep hsplit σ H

#print axioms s2440RootPermBar_agrees_rootPerm
#print axioms s2440RootPermBar_eq_permCongr_rootPerm
#print axioms s2440RootPermBar_cycleType_rootCycleType
#print axioms s2440_permBar_cycleType_eq_rootCycleType

end LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual
end
