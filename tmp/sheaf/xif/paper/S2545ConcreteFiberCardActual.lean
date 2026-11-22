import tmp.sheaf.xif.paper.S2544ConcretePermBarInvariantActual
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2541ConcreteRedRootActual
open LeanFormal.IUT.XiFPaper.S2542ConcreteRootFactorActual
open LeanFormal.IUT.XiFPaper.S2544ConcretePermBarInvariantActual
namespace LeanFormal.IUT.XiFPaper.S2545ConcreteFiberCardActual
attribute [local instance] Ideal.Quotient.field
open LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual
open LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual
open LeanFormal.IUT.XiFPaper.S2543FrobeniusOrbitActual
variable (f : R[X]) (p : Ideal R) [hp : p.IsMaximal]
  (P : Ideal S) [hP : P.IsPrime] [hPover : P.LiesOver p] [hPmax : P.IsMaximal]
  (hmonic : f.Monic) (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
  (hsplit : (f.map (algebraMap R L)).Splits)
  [Fintype (R ⧸ p)] [Fintype (S ⧸ P)]
  [DecidableEq (R ⧸ p)] [DecidableEq (S ⧸ P)]
include hmonic in
lemma g_root_implies_fbar_root
    (g : {g : (R ⧸ p)[X] // g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)})
    {x : S ⧸ P} (hx : x ∈ g.1.rootSet (S ⧸ P)) : x ∈ (fbar f p).rootSet (S ⧸ P) := by
  classical
  have hgmem := g.2
  rw [Polynomial.mem_normalizedFactors_iff (fbar_ne_zero f p hmonic)] at hgmem
  obtain ⟨hgirr, hgmonic, hgdvd⟩ := hgmem
  obtain ⟨h, hfbar_eq⟩ := hgdvd
  rw [mem_rootSet'] at hx ⊢
  refine ⟨Polynomial.map_monic_ne_zero
    (Polynomial.Monic.map (p := f) (Ideal.Quotient.mk p) hmonic), ?_⟩
  rw [hfbar_eq, aeval_mul, hx.2, zero_mul]
include hmonic hsplit P in
lemma fbar_splits : ((fbar f p).map (algebraMap (R ⧸ p) (S ⧸ P))).Splits := by
  have hS : (f.map (algebraMap R S)).Splits :=
    LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual.splits_over_S
      (f := f) (hmonic := hmonic) (hsplit := hsplit)
  have hmap := hS.map (Ideal.Quotient.mk P)
  rw [Polynomial.map_map] at hmap
  have hcomp : (Ideal.Quotient.mk P).comp (algebraMap R S) =
      (algebraMap (R ⧸ p) (S ⧸ P)).comp (Ideal.Quotient.mk p) := by
    ext x; exact (Ideal.Quotient.algebraMap_mk_of_liesOver P p x).symm
  rw [hcomp] at hmap
  simpa [fbar, Polynomial.map_map] using hmap

include hmonic in
noncomputable def fiberEquivRootSet
    (g : {g : (R ⧸ p)[X] // g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)}) :
    {y : (fbar f p).rootSet (S ⧸ P) //
      rootFactorMap (f := f) (p := p) (P := P) (hmonic := hmonic) y = g} ≃
      g.1.rootSet (S ⧸ P) :=
  (Equiv.subtypeEquiv (Equiv.refl ((fbar f p).rootSet (S ⧸ P)))
    (fun y => rootFactorMap_eq_iff f p P hmonic y g)).trans
  ((Equiv.subtypeSubtypeEquivSubtypeExists
      (p := fun x : S ⧸ P => x ∈ (fbar f p).rootSet (S ⧸ P))
      (q := fun y : {x : S ⧸ P // x ∈ (fbar f p).rootSet (S ⧸ P)} =>
        y.1 ∈ g.1.rootSet (S ⧸ P))).trans
    (Equiv.subtypeEquivRight (fun x =>
      ⟨fun h => h.2, fun hq =>
        ⟨g_root_implies_fbar_root f p P hmonic g hq, hq⟩⟩)))

include hmonic hsep hsplit in
lemma fiber_card
    (g : {g : (R ⧸ p)[X] // g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)}) :
    Fintype.card {y : (fbar f p).rootSet (S ⧸ P) //
      rootFactorMap (f := f) (p := p) (P := P) (hmonic := hmonic) y = g} =
      g.1.natDegree := by
  classical
  have hgmem := g.2
  rw [Polynomial.mem_normalizedFactors_iff (fbar_ne_zero f p hmonic)] at hgmem
  obtain ⟨hgirr, hgmonic, hgdvd⟩ := hgmem
  have hgsep : g.1.Separable :=
    Polynomial.Separable.of_dvd (by simpa [fbar] using hsep) hgdvd
  have hgsplit : (g.1.map (algebraMap (R ⧸ p) (S ⧸ P))).Splits := by
    refine Polynomial.Splits.of_dvd
      (f := g.1.map (algebraMap (R ⧸ p) (S ⧸ P)))
      (g := (fbar f p).map (algebraMap (R ⧸ p) (S ⧸ P)))
      (fbar_splits f p P hmonic hsplit) ?_ ?_
    · exact Polynomial.map_monic_ne_zero
        (Polynomial.Monic.map (p := f) (Ideal.Quotient.mk p) hmonic)
    · exact Polynomial.map_dvd _ hgdvd
  rw [Fintype.card_congr
    (fiberEquivRootSet (f := f) (p := p) (P := P) (hmonic := hmonic) g)]
  exact Polynomial.card_rootSet_eq_natDegree hgsep hgsplit

include hmonic in
lemma permBar_iterate_val
    (x : (fbar f p).rootSet (S ⧸ P)) (k : ℕ) :
    (((permBar (f := f) (p := p) (P := P))^[k]) x).1 =
      ((frobBar (p := p) (P := P))^[k]) x.1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        permBar_apply_val, ih]

include hmonic hsep hsplit in
lemma rootFactorMap_sameCycle
    {b : {g : (R ⧸ p)[X] // g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)}}
    {x y : (fbar f p).rootSet (S ⧸ P)}
    (hx : rootFactorMap (f := f) (p := p) (P := P) (hmonic := hmonic) x = b)
    (hy : rootFactorMap (f := f) (p := p) (P := P) (hmonic := hmonic) y = b) :
    (permBar (f := f) (p := p) (P := P)).SameCycle x y := by
  classical
  have hxr : x.1 ∈ b.1.rootSet (S ⧸ P) :=
    (rootFactorMap_eq_iff f p P hmonic x b).mp hx
  have hyr : y.1 ∈ b.1.rootSet (S ⧸ P) :=
    (rootFactorMap_eq_iff f p P hmonic y b).mp hy
  have hbmem := b.2
  rw [Polynomial.mem_normalizedFactors_iff (fbar_ne_zero f p hmonic)] at hbmem
  obtain ⟨hbirr, hbmonic, -⟩ := hbmem
  obtain ⟨k, hk⟩ :=
    LeanFormal.IUT.XiFPaper.S2543FrobeniusOrbitActual.exists_frobBar_iterate_eq_of_mem_rootSet
      (p := p) (P := P) b.1 hbirr hbmonic x.1 hxr y.1 hyr
  have hyx : y = ((permBar (f := f) (p := p) (P := P))^[k]) x := by
    apply Subtype.ext
    rw [permBar_iterate_val f p P hmonic x k]
    exact hk.2.symm
  have hsc : (permBar (f := f) (p := p) (P := P)).SameCycle x
      (((permBar (f := f) (p := p) (P := P))^[k]) x) := by
    have hpow : (((permBar (f := f) (p := p) (P := P))^[k]) x) =
        (((permBar (f := f) (p := p) (P := P)) ^ k) x) :=
      congrFun (Equiv.Perm.iterate_eq_pow (permBar (f := f) (p := p) (P := P)) k) x
    rw [hpow]
    exact (Equiv.Perm.sameCycle_pow_right
      (f := permBar (f := f) (p := p) (P := P)) (x := x) (y := x) (n := k)).mpr
      Equiv.Perm.SameCycle.rfl
  rwa [hyx]


include hmonic hsep hsplit in
theorem concrete_permBar_cycleType_fiber :
    (permBar (f := f) (p := p) (P := P)).cycleType =
      (Finset.univ.filter
        (fun g : {g : (R ⧸ p)[X] //
          g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)} =>
          2 ≤ g.1.natDegree)).val.map (fun g => g.1.natDegree) :=
  LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual.cycleType_eq_fiber_sizes
    (permBar (f := f) (p := p) (P := P))
    (rootFactorMap (f := f) (p := p) (P := P) (hmonic := hmonic))
    (fun g => g.1.natDegree)
    (fun x => rootFactorMap_permBar f p P hmonic x)
    (fun g => fiber_card f p P hmonic hsep hsplit g)
    (fun _ x y hx hy => rootFactorMap_sameCycle f p P hmonic hsep hsplit hx hy)

#print axioms concrete_permBar_cycleType_fiber
end LeanFormal.IUT.XiFPaper.S2545ConcreteFiberCardActual
end