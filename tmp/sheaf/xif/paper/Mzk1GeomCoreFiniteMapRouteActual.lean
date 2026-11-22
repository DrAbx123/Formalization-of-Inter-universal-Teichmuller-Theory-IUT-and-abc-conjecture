import tmp.sheaf.xif.paper.Mzk1GeomCoreFoundationActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreBridgeLegacyActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: finite-map construction / line bundle iso (Lead A435 last-mile 2) -> ported flt_test FiniteMapData structure (Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData.lean:19-55, fields U,V,f,g,m + affine/sup/mem/transition/finite/levelSet_free) + legacy Foundation scheme layer (FibreOverZeroEq/restated witness) + bridge adapters (Mzk1GeomCoreBridgeLegacyActual) + line-bundle carrier survey (S1504/PaperLineBundleCarrierActual/S1679 are paper-layer abstract carriers only) -> ROUTE INTERFACE (construction fields explicit) + assembly; full line-bundle iso and chart construction stay named gaps (no fake fields).

# Mzk1GeomCoreFiniteMapRouteActual — finite map to P1 / line bundle route (last-mile 2)

STATUS:
* `finiteMapData_of_construction`: PROVED constructor-from-fields for the ported
  FiniteMapData structure (exactly the 16 fields; this is the interface any future
  construction must populate).
* `preciseWitness_of_route`: PROVED conditional assembly: a FiniteMapData + bridge +
  positive degree + generic etaleness + pullback degree give the legacy restated precise
  witness (and its old recast).
* NAMED GAPS (recorded, not free fields):
  (a) finite-map-construction: produce U,V,f,g,m and all FiniteMapData fields from the
      function-field zero divisor g (two affine charts: U around the zeros, V around the
      poles; transition res_f_mul_res_g; finiteness/level-set grading).  No constructor
      exists in the ported trees; Mathlib has no projective-scheme morphism API.
  (b) psi^* O(1) = O(D) line bundle iso: no Cartier divisor / line bundle API on a
      general scheme in the tree; only the degree shadow `PullbackIsoDegree` (m = |D|)
      is formalized, plus paper-layer abstract carriers (S1504SourceLineBundleCarrier,
      PaperLineBundleCarrier, S1679CompleteODCarrier) that do NOT provide a scheme-level
      pullback isomorphism.  Exact gap documented as text, not as a free Prop.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapRouteActual

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCorePreciseActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual.SchemeLayer
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeLegacyActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

/-- **PROVED constructor-from-fields for the ported FiniteMapData.**  Any construction
route that produces the explicit chart data (U,V,f,g,m and the six compatibility
fields plus finiteness and level-set grading) yields a `Mzk1FiniteMapData`.  This is the
precise interface the missing finite-map construction has to populate. -/
def finiteMapData_of_construction
    (U V : C.Opens) (f : Γ(C, U)) (g : Γ(C, V)) (m : ℕ)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hsup : U ⊔ V = ⊤)
    (hmem : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base)
    (hinf : U ⊓ V = C.basicOpen f) (hinfg : U ⊓ V = C.basicOpen g)
    (hres : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (hfinf : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U;
      (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Finite)
    (hfing : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V;
      (Polynomial.aeval g : Polynomial R →ₐ[R] Γ(C, V)).toRingHom.Finite)
    (hlevel : ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
      letI := Scheme.TwoAffineOpenCover.algebraOfHom c U;
      Module.Finite S (S ⊗[R] Γ(C, U) ⧸
        Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) ∧
      Module.Free S (S ⊗[R] Γ(C, U) ⧸
        Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) ∧
      Module.finrank S (S ⊗[R] Γ(C, U) ⧸
        Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) = m) :
    Mzk1FiniteMapData c ε :=
  { U := U
    V := V
    f := f
    g := g
    m := m
    isAffineOpen_U := hU
    isAffineOpen_V := hV
    sup_eq_top := hsup
    mem_U_iff := hmem
    inf_eq_basicOpen := hinf
    inf_eq_basicOpen_g := hinfg
    res_f_mul_res_g := hres
    finite_f := hfinf
    finite_g := hfing
    levelSet_free := hlevel }

/-- **PROVED route assembly:** a finite-map datum together with the bridge (placePoint/
sectionMap compatibility), positive degree, generic etaleness and pullback degree yield
the legacy restated precise witness.  The bridge gives the non-vacuous fibre condition. -/
def preciseWitness_of_route {F : Type*} [Field F] {P : Type*} (ord : P → F → ℤ)
    (fm : Mzk1FiniteMapData c ε) (hdeg : 0 < fm.m)
    (B : FibreBridgeAbstract C Γ(C, fm.U) F (fm.U : Set C) fm.f
      (C.basicOpen fm.f : Set C) P ord)
    (D : Set C) (hunram : UnramifiedOverZero c ε fm)
    (hpull : PullbackIsoDegree c ε fm D) :
    Mzk1GeometricCoreWitnessPreciseRestated c ε
      (B.placePoint '' (B.Tplaces : Set P)) D :=
  restatedWitness_of_bridge ord fm hdeg B D hunram hpull

/-- **PROVED route -> old recast.** -/
theorem recast_of_route {F : Type*} [Field F] {P : Type*} (ord : P → F → ℤ)
    (fm : Mzk1FiniteMapData c ε) (hdeg : 0 < fm.m)
    (B : FibreBridgeAbstract C Γ(C, fm.U) F (fm.U : Set C) fm.f
      (C.basicOpen fm.f : Set C) P ord)
    (D : Set C) (hunram : UnramifiedOverZero c ε fm)
    (hpull : PullbackIsoDegree c ε fm D) :
    Mzk1GeometricCoreRecast c ε (B.placePoint '' (B.Tplaces : Set P)) D :=
  recast_of_restated ⟨preciseWitness_of_route ord fm hdeg B D hunram hpull⟩

/-- Exact text record of the two named gaps (not Prop fields, not assumptions). -/
def finiteMapRouteGapText : List String :=
  [ "GAP finite-map construction: populate U,V,f,g,m + 6 compatibility fields + finite_f/finite_g + levelSet_free from the function-field zero divisor; needs two affine charts (zeros/poles), TwoAffineOpenCover.algebraOfHom, transition res_f_mul_res_g, finiteness/level-set grading; no constructor in ported trees; Mathlib lacks projective-scheme morphism API",
    "GAP psi^*O(1)=O(D): no Cartier-divisor/line-bundle API on a general scheme; formalized only the degree shadow PullbackIsoDegree (m=|D|); paper-layer abstract carriers S1504SourceLineBundleCarrier/PaperLineBundleCarrier/S1679CompleteODCarrier do not provide the scheme-level pullback isomorphism" ]

def finiteMapRouteRows : List (String × String × String) :=
  [ ("FiniteMapData constructor-from-fields", "PROVED", "finiteMapData_of_construction (exact 16-field interface)")
  , ("bridge + fm => restated precise witness", "PROVED (conditional)", "preciseWitness_of_route")
  , ("bridge + fm => old recast", "PROVED (conditional)", "recast_of_route")
  , ("finite-map construction from function field", "NAMED GAP", "two affine charts around zeros/poles; no constructor API; see finiteMapRouteGapText #1")
  , ("psi^*O(1)=O(D) line bundle iso", "NAMED GAP", "no Cartier/line-bundle API; degree shadow PullbackIsoDegree only; paper carriers abstract; see finiteMapRouteGapText #2")
  , ("consumer chain", "READY", "restatedWitness_of_data/recast_of_restated from legacy Foundation; GenEll15 links via Foundation SchemeLayer") ]

theorem finiteMapRouteRows_length : finiteMapRouteRows.length = 6 := rfl

#check finiteMapData_of_construction
#check preciseWitness_of_route
#check recast_of_route
#check finiteMapRouteGapText
#check finiteMapRouteRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapRouteActual
end