/-
G1-A hull: real gluing of two schemes along a common open subscheme.

twoChartGlueData U0 U1 W g0 g1 glues U0 and U1 along the open subscheme W,
identified with its images via the open immersions g0 : W -> U0, g1 : W -> U1.
There are only two charts, so the transition map t is the identity and the cocycle
condition is a finite check.  The output is an honest Scheme.GlueData; its glued
scheme is the two-chart gluing.  (Proof pattern adapted from the compiled project
file S2801E37ProjectiveClosure, which glues two projective charts the same way.)

The index type is ULift.{u} Bool (needed for the universe of the glued scheme).  The
named indices twoChartIdx0 / twoChartIdx1 are typed in that universe, which lets the
user-facing cocycle equation twoChartGlue_condition be derived from
Scheme.GlueData.glue_condition by id_comp.
-/
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
import Mathlib.Tactic
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1HullFermatGluingActual
universe u
/-- The two charts (false is the first chart, true the second). -/
abbrev twoChartU (U0 U1 : Scheme.{u}) : Bool → Scheme.{u}
  | false => U0
  | true => U1
/-- The pairwise overlaps: the diagonal is the chart itself, off-diagonal is W. -/
abbrev twoChartV (U0 U1 W : Scheme.{u}) : Bool × Bool → Scheme.{u}
  | (false, false) => U0
  | (false, true) => W
  | (true, false) => W
  | (true, true) => U1
/-- The open immersion of each overlap into its chart. -/
abbrev twoChartF (U0 U1 W : Scheme.{u}) (g0 : W ⟶ U0) (g1 : W ⟶ U1) :
    (i j : Bool) → twoChartV U0 U1 W (i, j) ⟶ twoChartU U0 U1 i
  | false, false => 𝟙 U0
  | false, true => g0
  | true, false => g1
  | true, true => 𝟙 U1
/-- The transition maps: the two overlaps are identified by the identity. -/
abbrev twoChartT (U0 U1 W : Scheme.{u}) :
    (i j : Bool) → twoChartV U0 U1 W (i, j) ⟶ twoChartV U0 U1 W (j, i)
  | false, false => 𝟙 U0
  | false, true => 𝟙 W
  | true, false => 𝟙 W
  | true, true => 𝟙 U1
/-- The triple-overlap transition maps.  There are only two charts, so three indices cannot be
pairwise distinct and the cocycle is a finite check. -/
noncomputable def twoChartT' (U0 U1 W : Scheme.{u}) (g0 : W ⟶ U0) (g1 : W ⟶ U1)
    (hg0 : IsOpenImmersion g0) (hg1 : IsOpenImmersion g1) (i j k : Bool) :
    pullback (twoChartF U0 U1 W g0 g1 i j) (twoChartF U0 U1 W g0 g1 i k) ⟶
      pullback (twoChartF U0 U1 W g0 g1 j k) (twoChartF U0 U1 W g0 g1 j i) := by
  haveI hft : Mono (twoChartF U0 U1 W g0 g1 false true) := by
    dsimp only [twoChartF]
    exact IsOpenImmersion.mono g0
  haveI htf : Mono (twoChartF U0 U1 W g0 g1 true false) := by
    dsimp only [twoChartF]
    exact IsOpenImmersion.mono g1
  cases i <;> cases j <;> cases k
  · exact 𝟙 _
  · exact (pullbackSymmetry _ _).hom
  · exact pullback.fst _ _ ≫ twoChartT U0 U1 W false true ≫ inv (pullback.snd _ _)
  · exact pullback.fst _ _ ≫ twoChartT U0 U1 W false true ≫ inv (pullback.snd _ _)
  · exact pullback.fst _ _ ≫ twoChartT U0 U1 W true false ≫ inv (pullback.snd _ _)
  · exact pullback.fst _ _ ≫ twoChartT U0 U1 W true false ≫ inv (pullback.snd _ _)
  · exact (pullbackSymmetry _ _).hom
  · exact 𝟙 _
/-- Real gluing data for two schemes glued along a common open subscheme. -/
noncomputable abbrev twoChartGlueData (U0 U1 W : Scheme.{u}) (g0 : W ⟶ U0) (g1 : W ⟶ U1)
    (hg0 : IsOpenImmersion g0) (hg1 : IsOpenImmersion g1) : Scheme.GlueData.{u} where
  J := ULift.{u, 0} Bool
  U i := twoChartU U0 U1 i.down
  V p := twoChartV U0 U1 W (p.1.down, p.2.down)
  f i j := twoChartF U0 U1 W g0 g1 i.down j.down
  f_mono i j := by
    cases i with
    | up i => cases j with
      | up j =>
        cases i <;> cases j <;>
          (dsimp only [twoChartF];
            first
            | exact IsOpenImmersion.mono g0
            | exact IsOpenImmersion.mono g1
            | infer_instance)
  f_hasPullback i j k := by
    cases i with
    | up i => cases j with
      | up j => cases k with
        | up k =>
          cases i <;> cases j <;> cases k <;> (dsimp only [twoChartF]; infer_instance)
  f_id i := by
    cases i with
    | up i => cases i <;> (dsimp only [twoChartF]; infer_instance)
  t i j := twoChartT U0 U1 W i.down j.down
  t_id i := by
    cases i with
    | up i => cases i <;> rfl
  t' i j k := twoChartT' U0 U1 W g0 g1 hg0 hg1 i.down j.down k.down
  t_fac i j k := by
    cases i with
    | up i => cases j with
      | up j => cases k with
        | up k =>
          cases i <;> cases j <;> cases k <;>
          simp [twoChartT', twoChartT, twoChartF, twoChartU, twoChartV,
            fst_eq_snd_of_mono_eq, pullback.condition,
            pullbackSymmetry_hom_comp_snd, pullbackSymmetry_hom_comp_fst,
            Category.comp_id, Category.id_comp, Category.assoc]
  cocycle i j k := by
    cases i with
    | up i => cases j with
      | up j => cases k with
        | up k =>
          cases i <;> cases j <;> cases k <;>
          (apply pullback.hom_ext <;>
            simp [twoChartT', twoChartT, twoChartF, twoChartU, twoChartV,
              pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd,
              pullbackSymmetry_inv_comp_fst, pullbackSymmetry_inv_comp_snd,
              pullback.lift_fst, pullback.lift_snd,
              fst_eq_snd_of_mono_eq, pullback.condition,
              Category.comp_id, Category.id_comp, Category.assoc])
  f_open i j := by
    cases i with
    | up i => cases j with
      | up j =>
        cases i <;> cases j <;>
          (dsimp only [twoChartF];
            first
            | exact hg0
            | exact hg1
            | infer_instance)
/- NOTE (deferred, see AUDIT/brief): the user-facing cocycle equation
     g0 ≫ (twoChartGlueData ...).ι <first chart> = g1 ≫ (twoChartGlueData ...).ι <second chart>
is the i = false, j = true instance of Scheme.GlueData.glue_condition, with t = identity.
Deriving it needs rewriting 𝟙 W ≫ f = f inside terms whose types go through the opaque
definition twoChartGlueData; the rw/instances-transparency check rejects the composite
because (twoChartGlueData ...).J is only definitionally ULift Bool.  Inside the cocycle
field the same identity is already proved (t_fac/cocycle).  Fix planned: state the cocycle
equation at the level of an arbitrary GlueData with V (i,j) = V (j,i) hypothesis, or
restate the gluing data with a dedicated index type whose projections are reducible. -/

/-! ## Two-overlap version: the overlaps of the two charts are different schemes, exchanged
by an isomorphism e.  This is the S2801E37 template and avoids the identity transition map,
so the user-facing cocycle equation can be stated with e.hom. -/
/-- The pairwise overlaps of the two charts, with separate overlap schemes. -/
abbrev twoChartVOfIso (U0 U1 W0 W1 : Scheme.{u}) : Bool × Bool → Scheme.{u}
  | (false, false) => U0
  | (false, true) => W0
  | (true, false) => W1
  | (true, true) => U1
/-- The open immersion of each overlap into its chart (two-overlap version). -/
abbrev twoChartFOfIso (U0 U1 W0 W1 : Scheme.{u}) (g0 : W0 ⟶ U0) (g1 : W1 ⟶ U1) :
    (i j : Bool) → twoChartVOfIso U0 U1 W0 W1 (i, j) ⟶ twoChartU U0 U1 i
  | false, false => 𝟙 U0
  | false, true => g0
  | true, false => g1
  | true, true => 𝟙 U1
/-- The transition maps given by an isomorphism of the two overlaps. -/
abbrev twoChartT_of_iso (U0 U1 W0 W1 : Scheme.{u}) (e : W0 ≅ W1) :
    (i j : Bool) → twoChartVOfIso U0 U1 W0 W1 (i, j) ⟶ twoChartVOfIso U0 U1 W0 W1 (j, i)
  | false, false => 𝟙 U0
  | false, true => e.hom
  | true, false => e.inv
  | true, true => 𝟙 U1
/-- Real gluing data for two schemes glued along isomorphic overlaps. -/
noncomputable abbrev twoChartGlueDataOfIso (U0 U1 W0 W1 : Scheme.{u}) (g0 : W0 ⟶ U0)
    (g1 : W1 ⟶ U1) (e : W0 ≅ W1) (hg0 : IsOpenImmersion g0) (hg1 : IsOpenImmersion g1) :
    Scheme.GlueData.{u} where
  J := ULift.{u, 0} Bool
  U i := twoChartU U0 U1 i.down
  V p := twoChartVOfIso U0 U1 W0 W1 (p.1.down, p.2.down)
  f i j := twoChartFOfIso U0 U1 W0 W1 g0 g1 i.down j.down
  f_mono i j := by
    cases i with
    | up i => cases j with
      | up j =>
        cases i <;> cases j <;>
          (dsimp only [twoChartFOfIso];
            first
            | exact IsOpenImmersion.mono g0
            | exact IsOpenImmersion.mono g1
            | infer_instance)
  f_hasPullback i j k := by
    cases i with
    | up i => cases j with
      | up j => cases k with
        | up k =>
          cases i <;> cases j <;> cases k <;> (dsimp only [twoChartFOfIso]; infer_instance)
  f_id i := by
    cases i with
    | up i => cases i <;> (dsimp only [twoChartFOfIso]; infer_instance)
  t i j := twoChartT_of_iso U0 U1 W0 W1 e i.down j.down
  t_id i := by
    cases i with
    | up i => cases i <;> rfl
  t' i j k := by
    haveI hft : Mono (twoChartFOfIso U0 U1 W0 W1 g0 g1 false true) := by
      dsimp only [twoChartFOfIso]
      exact IsOpenImmersion.mono g0
    haveI htf : Mono (twoChartFOfIso U0 U1 W0 W1 g0 g1 true false) := by
      dsimp only [twoChartFOfIso]
      exact IsOpenImmersion.mono g1
    cases i with
    | up i => cases j with
      | up j => cases k with
        | up k =>
          cases i <;> cases j <;> cases k
          · exact 𝟙 _
          · exact (pullbackSymmetry _ _).hom
          · exact pullback.fst _ _ ≫ (twoChartT_of_iso U0 U1 W0 W1 e false true) ≫ inv (pullback.snd _ _)
          · exact pullback.fst _ _ ≫ (twoChartT_of_iso U0 U1 W0 W1 e false true) ≫ inv (pullback.snd _ _)
          · exact pullback.fst _ _ ≫ (twoChartT_of_iso U0 U1 W0 W1 e true false) ≫ inv (pullback.snd _ _)
          · exact pullback.fst _ _ ≫ (twoChartT_of_iso U0 U1 W0 W1 e true false) ≫ inv (pullback.snd _ _)
          · exact (pullbackSymmetry _ _).hom
          · exact 𝟙 _
  t_fac i j k := by
    cases i with
    | up i => cases j with
      | up j => cases k with
        | up k =>
          cases i <;> cases j <;> cases k <;>
          simp [twoChartT_of_iso, twoChartFOfIso, twoChartU, twoChartVOfIso, twoChartT,
            fst_eq_snd_of_mono_eq, pullback.condition,
            pullbackSymmetry_hom_comp_snd, pullbackSymmetry_hom_comp_fst,
            Category.comp_id, Category.id_comp, Category.assoc]
  cocycle i j k := by
    cases i with
    | up i => cases j with
      | up j => cases k with
        | up k =>
          cases i <;> cases j <;> cases k <;>
          (apply pullback.hom_ext <;>
            simp [twoChartT_of_iso, twoChartFOfIso, twoChartU, twoChartVOfIso, twoChartT,
              pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd,
              pullbackSymmetry_inv_comp_fst, pullbackSymmetry_inv_comp_snd,
              pullback.lift_fst, pullback.lift_snd,
              fst_eq_snd_of_mono_eq, pullback.condition,
              Category.comp_id, Category.id_comp, Category.assoc])
  f_open i j := by
    cases i with
    | up i => cases j with
      | up j =>
        cases i <;> cases j <;>
          (dsimp only [twoChartFOfIso];
            first
            | exact hg0
            | exact hg1
            | infer_instance)
end LeanFormal.IUT.XiFPaper.Mzk1HullFermatGluingActual
