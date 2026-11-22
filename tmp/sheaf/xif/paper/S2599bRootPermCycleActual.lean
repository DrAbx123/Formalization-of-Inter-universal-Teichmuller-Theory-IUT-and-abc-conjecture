/-
S2599b: the cycle type of the localized root permutation.

Setting (S2537): R10 = O_{F'}[1/10], T10 = O_L[1/10] (the integral closure of R10
in L10), f = f10' (S2577), p = p10, P = P10 W (S2663).  The localized redRoot
bridge of S2599a gives a bijection

  localizedRedRoot : f.rootSet L10 -> (fbar f p).rootSet (T10 / P).

This file defines the root permutation rootPermR sigma of sigma : Gal(L10/F')
acting on f.rootSet L10, and compares it with the q-Frobenius permutation
permBar on the residue roots (S2540, S2598c).

Main results:
* localizedRedRoot_smul: the actual commutation between the Galois action and
  the reduction map, localizedRedRoot (sigma • x) = permBar (localizedRedRoot x)
  (reusing the localized equivariance S2673_toS_smul and the reduction identity
  S2673_redRoot_smul);
* rootPermR_cycleType_eq_permBar: conditional cycle-type equality, from the
  commutation hypothesis (via the cross-type transport S2132cycleType_permCongr);
* rootPermR_cycleType_twelve: the unconditional cycle type {12}, by combining
  the conditional equality with S2598c_permBar_cycleType_12.

No sorry/axiom/native_decide/True is used.
-/
import tmp.sheaf.xif.paper.S2599aLocalizedRedRootActual
import tmp.sheaf.xif.paper.S2598cPermBar12Actual
import tmp.sheaf.xif.paper.S2597dToSSmulActual
import tmp.sheaf.xif.paper.S2673LocalizedOrbitSizeActual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 800000
open Polynomial NumberField

namespace LeanFormal.IUT.XiFPaper.S2599bRootPermCycleActual
attribute [local instance] Ideal.Quotient.field

abbrev R10 : Type := LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.R
abbrev T10 : Type := LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.S
abbrev K : Type := LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual.S1720Field
abbrev L10 : Type := LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual.S2057FiveDivisionField
abbrev f : R10[X] := LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.f10'
abbrev p : Ideal R10 := LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.p10
abbrev P : Ideal T10 := LeanFormal.IUT.XiFPaper.S2663P10PrimeActual.P10
  LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.W

local instance hp : p.IsMaximal :=
  LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.p10_max

local instance hPprime : P.IsPrime :=
  LeanFormal.IUT.XiFPaper.S2581S2543ParamsActual.P10_prime_self

local instance hPover : P.LiesOver p :=
  LeanFormal.IUT.XiFPaper.S2581S2543ParamsActual.P10_lies_p10_self

local instance hPmax : P.IsMaximal :=
  LeanFormal.IUT.XiFPaper.S2581S2543ParamsActual.P10_isMaximal_self

/-- The Galois action on the roots of f in L10, as a permutation. -/
noncomputable def rootPermR (sigma : Gal(L10/K)) : Equiv.Perm (f.rootSet L10) :=
  MulAction.toPermHom (Gal(L10/K)) (f.rootSet L10) sigma

/-- The reduction equivalence of S2599a: roots in L10 to roots mod P. -/
noncomputable def rootSetRedEquiv :
    f.rootSet L10 ≃
      (LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual.fbar f p).rootSet
        (T10 ⧸ P) :=
  Equiv.ofBijective
    (LeanFormal.IUT.XiFPaper.S2599aLocalizedRedRootActual.localizedRedRoot)
    (LeanFormal.IUT.XiFPaper.S2599aLocalizedRedRootActual.localizedRedRoot_bijective)

lemma rootPermR_apply (sigma : Gal(L10/K)) (x : f.rootSet L10) :
    rootPermR sigma x = sigma • x := by
  apply Subtype.ext
  simp only [rootPermR, MulAction.toPermHom_apply, MulAction.toPerm_apply,
    Polynomial.rootSet.coe_smul, AlgEquiv.smul_def]

/-- The actual commutation: the localized reduction intertwines the Galois
action on the L10-roots with the q-Frobenius permutation permBar on the
residue roots. -/
theorem localizedRedRoot_smul (sigma : Gal(L10/K))
    (H : IsArithFrobAt R10 sigma P) (x : f.rootSet L10) :
    LeanFormal.IUT.XiFPaper.S2599aLocalizedRedRootActual.localizedRedRoot
        (sigma • x) =
      LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual.permBar (f := f) (p := p) (P := P)
        (LeanFormal.IUT.XiFPaper.S2599aLocalizedRedRootActual.localizedRedRoot x) := by
  change LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual.redRoot
      (f := f) (p := p) (P := P)
      (hmonic := LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hmonic)
      (LeanFormal.IUT.XiFPaper.S2597RootSetEquivActual.toS (R := R10) (S := T10) (L := L10)
        f LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hmonic
        (LeanFormal.IUT.XiFPaper.S2599aLocalizedRedRootActual.f_natDegree_ne_zero) (sigma • x)) =
    LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual.permBar (f := f) (p := p) (P := P)
      (LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual.redRoot
        (f := f) (p := p) (P := P)
        (hmonic := LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hmonic)
        (LeanFormal.IUT.XiFPaper.S2597RootSetEquivActual.toS (R := R10) (S := T10) (L := L10)
          f LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hmonic
          (LeanFormal.IUT.XiFPaper.S2599aLocalizedRedRootActual.f_natDegree_ne_zero) x))
  rw [LeanFormal.IUT.XiFPaper.S2673LocalizedOrbitSizeActual.S2673_toS_smul
    f LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hmonic
    (LeanFormal.IUT.XiFPaper.S2599aLocalizedRedRootActual.f_natDegree_ne_zero) sigma x]
  exact LeanFormal.IUT.XiFPaper.S2673LocalizedOrbitSizeActual.S2673_redRoot_smul
    (f := f) (p := p) (P := P)
    LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hmonic
    LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hsep
    LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hsplit sigma H
    (LeanFormal.IUT.XiFPaper.S2597RootSetEquivActual.toS (R := R10) (S := T10) (L := L10)
      f LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hmonic
      (LeanFormal.IUT.XiFPaper.S2599aLocalizedRedRootActual.f_natDegree_ne_zero) x)

/-- Conditional cycle-type equality: if the localized reduction commutes with
the Galois action (hcomm), then rootPermR sigma and permBar have the same cycle
type. -/
theorem rootPermR_cycleType_eq_permBar
    (hcomm : ∀ (sigma : Gal(L10/K)) (_ : IsArithFrobAt R10 sigma P)
      (x : f.rootSet L10),
      LeanFormal.IUT.XiFPaper.S2599aLocalizedRedRootActual.localizedRedRoot
          (sigma • x) =
        LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual.permBar (f := f) (p := p) (P := P)
          (LeanFormal.IUT.XiFPaper.S2599aLocalizedRedRootActual.localizedRedRoot x))
    (sigma : Gal(L10/K)) (H : IsArithFrobAt R10 sigma P) :
    (rootPermR sigma).cycleType =
      (LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual.permBar
        (f := f) (p := p) (P := P)).cycleType := by
  classical
  let e := rootSetRedEquiv
  have hconj : e.permCongr (rootPermR sigma) =
      LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual.permBar (f := f) (p := p) (P := P) := by
    apply Equiv.ext
    intro z
    rw [Equiv.permCongr_apply]
    obtain ⟨y, rfl⟩ := e.surjective z
    rw [Equiv.symm_apply_apply]
    show LeanFormal.IUT.XiFPaper.S2599aLocalizedRedRootActual.localizedRedRoot
        (rootPermR sigma y) =
      LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual.permBar (f := f) (p := p) (P := P)
        (LeanFormal.IUT.XiFPaper.S2599aLocalizedRedRootActual.localizedRedRoot y)
    rw [rootPermR_apply]
    exact hcomm sigma H y
  calc (rootPermR sigma).cycleType
      = (e.permCongr (rootPermR sigma)).cycleType :=
        (LeanFormal.IUT.XiFPaper.S2132FrobCycleActual.S2132cycleType_permCongr
          e (rootPermR sigma)).symm
    _ = (LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual.permBar
          (f := f) (p := p) (P := P)).cycleType := by rw [hconj]

/-- The concrete permBar of S2598c is exactly the permBar used here. -/
theorem permBar_cycleType_twelve :
    (LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual.permBar
      (f := f) (p := p) (P := P)).cycleType = ({12} : Multiset ℕ) := by
  change (LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual.permBar
      (f := LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.f10')
      (p := LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.p10)
      (P := LeanFormal.IUT.XiFPaper.S2663P10PrimeActual.P10
        LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.W)).cycleType =
    ({12} : Multiset ℕ)
  exact LeanFormal.IUT.XiFPaper.S2598cPermBar12Actual.S2598c_permBar_cycleType_12

/-- The cycle type of the localized root permutation is {12}. -/
theorem rootPermR_cycleType_twelve (sigma : Gal(L10/K))
    (H : IsArithFrobAt R10 sigma P) :
    (rootPermR sigma).cycleType = ({12} : Multiset ℕ) := by
  rw [rootPermR_cycleType_eq_permBar
    (fun sigma H x => localizedRedRoot_smul sigma H x) sigma H]
  exact permBar_cycleType_twelve

#check rootPermR
#check rootSetRedEquiv
#check rootPermR_apply
#check localizedRedRoot_smul
#check rootPermR_cycleType_eq_permBar
#check permBar_cycleType_twelve
#check rootPermR_cycleType_twelve
#print axioms localizedRedRoot_smul
#print axioms rootPermR_cycleType_eq_permBar
#print axioms permBar_cycleType_twelve
#print axioms rootPermR_cycleType_twelve

end LeanFormal.IUT.XiFPaper.S2599bRootPermCycleActual
end
