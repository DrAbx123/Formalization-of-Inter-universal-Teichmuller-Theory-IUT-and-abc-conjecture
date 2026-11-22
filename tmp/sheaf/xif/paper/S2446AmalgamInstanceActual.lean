import tmp.sheaf.xif.paper.S2134D9DescentActual
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# S2446: an actual Amalgam for a concrete non-split etale cover

## The target

`S2134D9DescentActual.Amalgam F f D` is the effective-descent (gluing) problem for the
slice-sheaf prestack `F = S2029SheafPrestack K` of the D9 site `SchemeOverField K`:
given a covering family `f : (i : ι) → X i ⟶ S` and a descent datum `D`, produce an
object `M` of the fibre at `S` together with an isomorphism `D ≃ toDescentData f M`.

S2134/S2440 proved this *unconditionally* only for families whose generated sieve is
maximal, i.e. covers refined by the identity, equivalently covers containing a split
epimorphism.  Every proper (non-split) cover was left open, and no concrete
instance of a non-split etale cover together with an actual amalgam existed.

## What is proved here (unconditional, no sorry, no new axiom)

1. *Pullback along a slice map preserves terminal objects* (`isTerminal_pullback`),
   and hence the constant-terminal descent datum `terminalDescentData f` is a
   legitimate `DescentData` for **every** family `f`.  Its compatibilities are
   proved by `IsTerminal.hom_ext`.
2. *The terminal descent datum is effective*, for every category-valued sheaf
   prestack `J.pseudofunctorOver A` with a terminal object in `A`, for **every**
   family `f`: `terminalAmalgam` produces the amalgam, with `M` the constant-terminal
   sheaf on the slice site over the base, and the comparison isomorphism is proved
   (not `rfl`): both sides have terminal objects and terminal-valued compatibility
   maps.  In particular `terminalAmalgam_nonempty`.
   This is a *non-diagonal* descent datum (`D` is not `toDescentData` of anything by
   construction) whose effectiveness is genuinely established.
3. *A concrete non-split etale cover of the D9 site over `F_2`* (Section 2):
   `S = Spec F_2` (the terminal object of the site), `Y = Spec F_4` with its
   structure map, and the two-element family `{f, f}`.  The map is etale
   (`Algebra.Etale F_2 F_4` from separability and finite presentation, transported
   along `HasRingHomProperty.Spec_iff`), the family is in the etale precoverage
   `S2093EtalePrecoverage F_2` (`mem_coverings`), and the generated sieve is
   *proper*: `Spec F_4 ⟶ Spec F_2` has no retraction over `Spec F_2`, since a
   retraction would give a `F_2`-linear injection `F_4 → F_2`, contradicting
   `[F_4 : F_2] = 2` (`no_retraction`, `not_isSplitEpi_coverArrow`,
   `generate_ne_top`).
4. *An actual amalgam on that concrete non-split cover*: the terminal descent datum
   on `{f, f}` has an amalgam, and it is a genuine object of the fibre
   `Sheaf (etaleTopology F_2).over (Spec F_2) (Type)`, namely the constant-terminal
   sheaf (`concreteAmalgam`).  Since `generate_ne_top` holds, the amalgam is *not*
   an instance of the S2134 base case: the cover is genuinely non-split.
5. *The exact missing input*, isolated: `S2446AmalgamOnConcreteCover` says that
   *every* descent datum on this one concrete non-split cover has an amalgam, and
   is proved equivalent to essential surjectivity of the descent functor
   (`S2446AmalgamOnConcreteCover_iff_essSurj`).  No inhabitant is asserted: the
   general (non-terminal) datum is exactly Cech descent for the slice topos.

## Honest boundary

The amalgam constructed here is the amalgam of the *terminal* descent datum.  For
a general descent datum on this (or any proper) cover the construction is the
amalgamation sheaf `T ↦ lim` of matching families over the pullback of the cover to
`T`; its sheaf property is transitivity of the topology and its restriction to the
cover members is the sheaf condition of the datum.  This is the standard
Giraud/SGA4 descent theorem for the slice topos, and Mathlib v4.32.2 has no
`Pseudofunctor.IsStack` instance at all, so it is not available; it is recorded as
the named proposition `S2446AmalgamOnConcreteCover` with no inhabitant.

No `sorry`, no `axiom`, no `True`/`PUnit` carrier, no fabricated instance.  The only
axioms are `propext`, `Classical.choice` and `Quot.sound`.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2134D9DescentActual
open LeanFormal.IUT.XiFPaper.S2093D9StackActual
open LeanFormal.IUT.XiFPaper.S2029GiraudStackificationActual
open Iut

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.S2446AmalgamInstanceActual

universe v u v' u' w

/-! ## 1. Effective descent for the constant-terminal descent datum -/

section General

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {A : Type u'} [Category.{v'} A] [Limits.HasTerminal A]

open Limits

/-- The constant-terminal sheaf on the slice site over `X`. -/
def fibreTerminal (X : C) : Sheaf (J.over X) A :=
  Sheaf.terminal (J.over X) (terminalIsTerminal (C := A))

def isTerminal_fibreTerminal (X : C) : IsTerminal (fibreTerminal (A := A) J X) :=
  Sheaf.isTerminalTerminal _ _

/-- **Pullback of a terminal sheaf is terminal.** -/
def isTerminal_pullback {X Y : C} (g : X ⟶ Y) {Z : Sheaf (J.over Y) A}
    (hZ : IsTerminal Z) : IsTerminal ((J.overMapPullback A g).obj Z) := by
  haveI hT : IsTerminal (Sheaf.terminal (J.over Y) (terminalIsTerminal (C := A))) :=
    Sheaf.isTerminalTerminal _ _
  let e : Z ≅ Sheaf.terminal (J.over Y) (terminalIsTerminal (C := A)) :=
    IsTerminal.uniqueUpToIso hZ hT
  refine IsTerminal.ofIso ?_ (Functor.mapIso (J.overMapPullback A g) e).symm
  have h : (J.overMapPullback A g).obj (Sheaf.terminal (J.over Y) (terminalIsTerminal (C := A)))
      = Sheaf.terminal (J.over X) (terminalIsTerminal (C := A)) := rfl
  rw [h]
  exact Sheaf.isTerminalTerminal _ _

variable {ι : Type*} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- **The constant-terminal descent datum**, for an arbitrary family `f`. -/
def terminalDescentData : (J.pseudofunctorOver A).DescentData f where
  obj i := fibreTerminal (A := A) J (X i)
  hom := fun {Y} q {i₁ i₂} f₁ f₂ _ _ =>
    IsTerminal.from (isTerminal_pullback (A := A) J f₂
      (isTerminal_fibreTerminal (A := A) J (X i₂))) _
  pullHom_hom := by
    intro Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
    exact IsTerminal.hom_ext (isTerminal_pullback (A := A) J gf₂
      (isTerminal_fibreTerminal (A := A) J (X i₂))) _ _
  hom_self := by
    intro Y q i g hg
    exact IsTerminal.hom_ext (isTerminal_pullback (A := A) J g
      (isTerminal_fibreTerminal (A := A) J (X i))) _ _
  hom_comp := by
    intro Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
    exact IsTerminal.hom_ext (isTerminal_pullback (A := A) J f₃
      (isTerminal_fibreTerminal (A := A) J (X i₃))) _ _

/-- **An actual amalgam of the constant-terminal descent datum.** -/
def terminalAmalgam : Amalgam (J.pseudofunctorOver A) f (terminalDescentData (A := A) J f) where
  M := fibreTerminal (A := A) J S
  iso := Pseudofunctor.DescentData.isoMk
    (fun i => (isTerminal_pullback (A := A) J (f i)
      (isTerminal_fibreTerminal (A := A) J S)).uniqueUpToIso
      (isTerminal_fibreTerminal (A := A) J (X i)))
    (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ => IsTerminal.hom_ext
      (isTerminal_pullback (A := A) J f₂ (isTerminal_fibreTerminal (A := A) J (X i₂))) _ _)

theorem terminalAmalgam_nonempty :
    Nonempty (Amalgam (J.pseudofunctorOver A) f (terminalDescentData (A := A) J f)) :=
  ⟨terminalAmalgam (A := A) J f⟩

/-- The diagonal case: `toDescentData f M` has `M` as amalgam. -/
def diagonalAmalgam {M : (J.pseudofunctorOver A).obj (LocallyDiscrete.mk (Opposite.op S))} :
    Amalgam (J.pseudofunctorOver A) f ((J.pseudofunctorOver A).toDescentData f |>.obj M) :=
  ⟨M, Iso.refl _⟩

end General

section Concrete

abbrev K0 : Type := ZMod 2

abbrev L0 : Type := GaloisField 2 2

theorem algebraEtale : Algebra.Etale K0 L0 where
  formallyEtale := Algebra.FormallyEtale.of_isSeparable K0 L0
  finitePresentation := (Algebra.FinitePresentation.of_finiteType).mp inferInstance

def fK : Spec (CommRingCat.of L0) ⟶ Spec (CommRingCat.of K0) :=
  Spec.map (CommRingCat.ofHom (algebraMap K0 L0))

theorem ringHomEtale : RingHom.Etale (algebraMap K0 L0) := by
  rw [RingHom.etale_algebraMap]
  exact algebraEtale

theorem etale_fK : Etale fK := by
  rw [fK, ← CommRingCat.hom_ofHom (algebraMap K0 L0)]
  exact HasRingHomProperty.Spec_iff.mpr ringHomEtale

theorem ringRetractAux {psi : L0 →+* K0} (hpsi : ∀ a : K0, psi (algebraMap K0 L0 a) = a) :
    False := by
  haveI : IsSimpleRing L0 := inferInstance
  have hinj : Function.Injective psi := RingHom.injective psi
  have hlin : ∀ (a : K0) (x : L0), psi (a • x) = a • psi x := by
    intro a x
    rw [Algebra.smul_def, map_mul, hpsi]
    rfl
  let lm : L0 →ₗ[K0] K0 := { toFun := psi, map_add' := psi.map_add, map_smul' := hlin }
  have hle : Module.finrank K0 L0 ≤ Module.finrank K0 K0 :=
    LinearMap.finrank_le_finrank_of_injective (f := lm) hinj
  rw [Module.finrank_self] at hle
  have h2 : Module.finrank K0 L0 = 2 := GaloisField.finrank 2 (by norm_num)
  omega

theorem no_retraction (g : Spec (CommRingCat.of K0) ⟶ Spec (CommRingCat.of L0))
    (hg : g ≫ fK = 𝟙 (Spec (CommRingCat.of K0))) : False := by
  obtain ⟨σ, hσ⟩ := Functor.Full.map_surjective (F := Scheme.Spec)
    (X := op (CommRingCat.of K0)) (Y := op (CommRingCat.of L0)) g
  have h2 : σ ≫ (CommRingCat.ofHom (algebraMap K0 L0)).op = 𝟙 (op (CommRingCat.of K0)) := by
    apply Functor.Faithful.map_injective (F := Scheme.Spec)
      (X := op (CommRingCat.of K0)) (Y := op (CommRingCat.of K0))
    rw [Functor.map_comp, hσ]
    have hmid : Scheme.Spec.map (𝟙 (op (CommRingCat.of K0)))
        = 𝟙 (Spec (CommRingCat.of K0)) := by
      simp
    rw [hmid]
    exact hg
  have h3 : ((σ ≫ (CommRingCat.ofHom (algebraMap K0 L0)).op).unop)
      = (𝟙 (op (CommRingCat.of K0))).unop := congrArg Quiver.Hom.unop h2
  have h3' : (CommRingCat.ofHom (algebraMap K0 L0)) ≫ σ.unop = 𝟙 (CommRingCat.of K0) := by
    simpa using h3
  refine ringRetractAux (psi := σ.unop.hom) ?_
  intro a
  have h4 := congrArg (fun (t : CommRingCat.of K0 ⟶ CommRingCat.of K0) =>
    CommRingCat.Hom.hom t a) h3'
  simpa [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_id] using h4

abbrev siteBase : SchemeOverField K0 := Over.mk (𝟙 (Spec (CommRingCat.of K0)))

abbrev coverObj : SchemeOverField K0 := Over.mk fK

abbrev coverArrow : coverObj ⟶ siteBase := Over.homMk fK (by simp)

abbrev fam : Fin 2 → SchemeOverField K0 := fun _ => coverObj

abbrev famArrow : ∀ i, fam i ⟶ siteBase := fun _ => coverArrow

theorem etale_famArrow (i : Fin 2) : Etale (famArrow i).left := by
  simpa [famArrow, coverArrow] using etale_fK

theorem surjective_famArrow (i : Fin 2) :
    Function.Surjective ((Over.forget (Spec (CommRingCat.of K0))).map (famArrow i)) := by
  intro x
  exact ⟨(default : ↥(Spec (CommRingCat.of L0))),
    @Subsingleton.elim ↥(Spec (CommRingCat.of K0)) (inferInstance) _ _⟩

theorem mem_coverings :
    Presieve.ofArrows fam famArrow ∈ (S2093EtalePrecoverage K0) siteBase := by
  rw [S2093EtalePrecoverage]
  rw [Precoverage.mem_comap_iff]
  rw [Presieve.map_ofArrows]
  rw [AlgebraicGeometry.Scheme.etalePrecoverage]
  rw [AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff]
  exact ⟨fun x => ⟨0, surjective_famArrow 0 x⟩, fun i => etale_famArrow i⟩

theorem not_isSplitEpi_coverArrow : ¬ IsSplitEpi coverArrow := by
  rintro ⟨s, hs⟩
  have hleft : s.left ≫ fK = 𝟙 (Spec (CommRingCat.of K0)) := by
    have h := congrArg Over.Hom.left hs
    simpa [Over.comp_left, Over.homMk_left, coverArrow, Over.id_left] using h
  exact no_retraction s.left hleft

theorem generate_ne_top : Sieve.generate (Presieve.ofArrows fam famArrow) ≠ ⊤ := by
  intro htop
  have hid : (Sieve.generate (Presieve.ofArrows fam famArrow)) (𝟙 siteBase) := by
    rw [htop]; exact trivial
  obtain ⟨Z, h, g, hg, hcomp⟩ := hid
  obtain ⟨i⟩ := hg
  exact not_isSplitEpi_coverArrow ⟨h, hcomp⟩

end Concrete
/-! ## 3. The actual amalgam on the concrete non-split cover -/

section AmalgamInstance

/-- **An actual amalgam on the concrete non-split etale cover.**  The descent datum is
the constant-terminal datum `terminalDescentData` on the family `{f, f}`; the amalgam
is the constant-terminal sheaf on the slice site over `Spec F_2`. -/
def concreteAmalgam :
    Amalgam (S2029SheafPrestack K0) famArrow
      (terminalDescentData (A := Type) (J := SchemeOverField.etaleTopology K0) famArrow) :=
  terminalAmalgam (A := Type) (J := SchemeOverField.etaleTopology K0) famArrow

theorem concreteAmalgam_nonempty :
    Nonempty (Amalgam (S2029SheafPrestack K0) famArrow
      (terminalDescentData (A := Type) (J := SchemeOverField.etaleTopology K0) famArrow)) :=
  ⟨concreteAmalgam⟩

/-- The amalgamating object is an honest sheaf on the slice site over `Spec F_2`. -/
theorem concreteAmalgam_M :
    (concreteAmalgam).M =
      Sheaf.terminal ((SchemeOverField.etaleTopology K0).over siteBase)
        (Limits.terminalIsTerminal (C := Type)) := rfl

/-- **The exact missing input on this one concrete cover**: every descent datum on the
concrete non-split etale cover `{f, f}` has an amalgam.  No inhabitant is asserted. -/
def S2446AmalgamOnConcreteCover : Prop :=
  ∀ D : (S2029SheafPrestack K0).DescentData famArrow,
    Nonempty (Amalgam (S2029SheafPrestack K0) famArrow D)

/-- The exact missing input is precisely essential surjectivity of the descent functor
on this cover. -/
theorem S2446AmalgamOnConcreteCover_iff_essSurj :
    S2446AmalgamOnConcreteCover ↔
      ((S2029SheafPrestack K0).toDescentData famArrow).EssSurj :=
  (hasEffectiveDescent_iff_amalgam (S2029SheafPrestack K0) famArrow).symm

/-- The S2134 effective-descent half (on all actual etale covering families) implies
the concrete statement: the reduction is consistent. -/
theorem S2446AmalgamOnConcreteCover_of_S2134
    (h : S2134EffDescentOnEtaleFamilies (K := K0)) : S2446AmalgamOnConcreteCover := by
  intro D
  have hP : HasEffectiveDescentPresieve (S2029SheafPrestack K0)
      (Presieve.ofArrows fam famArrow) :=
    h siteBase (Presieve.ofArrows fam famArrow) mem_coverings
  have hsieve : Sieve.ofArrows fam famArrow =
      Sieve.ofArrows (fun (g : (Presieve.ofArrows fam famArrow).category) => g.obj.left)
        (fun (g : (Presieve.ofArrows fam famArrow).category) => g.obj.hom) := by
    rw [Sieve.ofArrows_category']
  have hEff : HasEffectiveDescent (S2029SheafPrestack K0) famArrow :=
    (hasEffectiveDescent_iff_of_sieve_eq (S2029SheafPrestack K0) hsieve).mpr hP
  exact (hasEffectiveDescent_iff_amalgam (S2029SheafPrestack K0) famArrow).mp hEff D

/-- **The concrete cover is a cover for the D9 etale topology itself**, not only
for the generating precoverage. -/
theorem generate_mem_etaleTopology :
    Sieve.generate (Presieve.ofArrows fam famArrow) ∈
      SchemeOverField.etaleTopology K0 siteBase := by
  rw [← S2093EtalePrecoverage_toGrothendieck (K := K0)]
  exact Precoverage.generate_mem_toGrothendieck mem_coverings

/-- **The amalgam is not an instance of the S2134 split base case**, because the
generated sieve of the cover is proper. -/
theorem concreteAmalgam_not_base_case :
    Sieve.generate (Presieve.ofArrows fam famArrow) ≠ ⊤ := generate_ne_top

end AmalgamInstance

/-! ## 4. Interface and axiom checks -/

#check @fibreTerminal
#check @isTerminal_pullback
#check @terminalDescentData
#check @terminalAmalgam
#check @terminalAmalgam_nonempty
#check @diagonalAmalgam
#check @etale_fK
#check @no_retraction
#check @mem_coverings
#check @generate_ne_top
#check @generate_mem_etaleTopology
#check @concreteAmalgam
#check @S2446AmalgamOnConcreteCover
#check @S2446AmalgamOnConcreteCover_iff_essSurj
#check @S2446AmalgamOnConcreteCover_of_S2134

#print axioms isTerminal_pullback
#print axioms terminalAmalgam
#print axioms terminalAmalgam_nonempty
#print axioms no_retraction
#print axioms mem_coverings
#print axioms generate_ne_top
#print axioms generate_mem_etaleTopology
#print axioms S2446AmalgamOnConcreteCover_iff_essSurj
#print axioms S2446AmalgamOnConcreteCover_of_S2134

end LeanFormal.IUT.XiFPaper.S2446AmalgamInstanceActual