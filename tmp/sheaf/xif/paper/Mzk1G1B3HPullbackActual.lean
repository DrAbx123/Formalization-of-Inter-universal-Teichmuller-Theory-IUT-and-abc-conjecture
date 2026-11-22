/-
  B3 (h-pullback) -- the generic statement `h^*O(1) = O(natDegree h)` on `P¹` at the Cech level.

  ## Route

  We use the two-chart Cech formalism of `TwoChartCech` (`Cover`, `Sections`,
  `lineBundle`, `SectionsIso`) together with the coboundary criterion
  `TwoChartCech.Cover.lineBundle_iso_of_mul` of
  `Mzk1TwoChartCechLineBundleIsoActual`: two transition units `t`, `t'` define
  isomorphic line bundles as soon as `t' * ρ1 a1 = ρ0 a0 * t` for units
  `a0 : A0ˣ`, `a1 : A1ˣ`.

  ## The `h`-refined cover of `P¹`

  For a nonzero polynomial `h : ℚ[λ]` (kept as a parameter; `d` is meant to be
  `h.natDegree`) the three rings of the refined cover are

  * `A0  = Localization.Away h`                     over `ℚ[λ]`  (chart `λ` on `D(h)`),
  * `A1  = P1Overlap = Localization.Away X`         over `ℚ[λ]`  (the torus `ℚ[λ,λ⁻¹]`,
    on which the coordinate `λ` itself is a unit),
  * `A01 = Localization.Away (algebraMap ℚ[λ] P1Overlap h)` over `P1Overlap`
    (the overlap on which both `λ` and `h` are units).

  The map `ρ0 : A0 → A01` is the localization lift of
  `ℚ[λ] → P1Overlap → A01` at `h` (both `λ` and `h` are invertible in `A01`), and
  `ρ1 : A1 → A01` is the localization `algebraMap P1Overlap A01` (viewed as a
  `ℚ`-algebra map through the tower `ℚ → P1Overlap → A01`; it agrees with
  `IsScalarTower.toAlgHom ℚ P1Overlap A01`, and is constructed here directly as the
  composite so that it only depends on the algebra structures).

  ## Transition units

  * `hUnitA01 h` is the unit of `h` in `A01`: this is the transition unit of `h^*O(1)`;
  * `xUnitA1` is the unit `λ` of `P1Overlap`, and `xUnitA01 h` its image in `A01`;
  * `odUnit h d = (xUnitA01 h)^d` is the transition unit of `O(d)`, `d = h.natDegree`;
  * `a0 h` is the unit `h` of `A0`, `a1 d = (xUnitA1)^d` the unit `λ^d` of `A1`.

  Because `h` is a unit of `A0` and `λ` a unit of `A1`, both transition units are
  Cech coboundaries on the refined cover, and the coboundary relation
  `hUnitA01 = ρ0 (a0) * odUnit * (ρ1 (a1))⁻¹` holds with `a0 = h`, `a1 = λ^d`:

      hUnitA01 * ρ1 a1 = ρ0 a0 * odUnit      (`transition_relation`).

  This is the key computation; `lineBundle_iso_of_mul` then gives

      h^*O(1) = lineBundle hUnitA01  ≅  lineBundle (odUnit h h.natDegree) = O(natDegree h).

  No `sorry`; the axiom footprint is checked at the end of the file.
-/
import tmp.sheaf.xif.paper.Mzk1TwoChartCechLineBundleIsoActual
import tmp.sheaf.xif.paper.Mzk1G1B3CoverActual
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic

noncomputable section

set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.Mzk1G1B3HPullbackActual

open LeanFormal.IUT.XiFPaper.Mzk1G1B3CoverActual

variable (h : Polynomial ℚ)

/-! ## The three rings of the `h`-refined cover -/

/-- `A0` of the `h`-refined cover: the first chart `ℚ[λ]` of `P¹` localized at `h`,
i.e. the first chart restricted to the principal open `D(h)`. -/
noncomputable abbrev p1HChart0 : Type := Localization.Away h

/-- `A1` of the `h`-refined cover: the overlap `ℚ[λ,λ⁻¹]` of the standard two-chart
cover of `P¹` (the torus), on which `λ` is a unit. -/
abbrev p1HChart1 : Type := P1Overlap

/-- `A01` of the `h`-refined cover: `P1Overlap` localized at the image of `h`.  This is
the ring on which both `λ` and `h` are units. -/
noncomputable abbrev p1HOverlap : Type :=
  Localization.Away (algebraMap (Polynomial ℚ) P1Overlap h)

/-! ## `ρ0 : A0 → A01` -/

/-- The `ℚ`-algebra map `ℚ[λ] → A01` underlying `ρ0`: first chart `ℚ[λ]`, then the
torus `P1Overlap`, then `A01`. -/
noncomputable def chart0ToHOverlap : Polynomial ℚ →ₐ[ℚ] p1HOverlap h where
  toRingHom :=
    (algebraMap P1Overlap (p1HOverlap h)).comp (algebraMap (Polynomial ℚ) P1Overlap)
  commutes' r := by
    have hc :
        ((algebraMap P1Overlap (p1HOverlap h)).comp
            (algebraMap (Polynomial ℚ) P1Overlap)).comp (algebraMap ℚ (Polynomial ℚ)) =
          algebraMap ℚ (p1HOverlap h) := RingHom.ext_rat _ _
    exact RingHom.congr_fun hc r

/-- `chart0ToHOverlap` is the composite of the two structure maps. -/
theorem chart0ToHOverlap_apply (x : Polynomial ℚ) :
    chart0ToHOverlap h x =
      algebraMap P1Overlap (p1HOverlap h) (algebraMap (Polynomial ℚ) P1Overlap x) :=
  rfl

/-- The image of `h` in `A01` is a unit: it is the localized element defining `A01`. -/
theorem chart0ToHOverlap_isUnit : IsUnit (chart0ToHOverlap h h) := by
  rw [chart0ToHOverlap_apply]
  exact IsLocalization.Away.algebraMap_isUnit (S := p1HOverlap h)
    (x := algebraMap (Polynomial ℚ) P1Overlap h)

/-- `ρ0 : A0 → A01` of the `h`-refined cover: the localization lift at `h` of
`ℚ[λ] → P1Overlap → A01` (both `λ` and `h` are invertible in `A01`). -/
noncomputable def rho0 : p1HChart0 h →ₐ[ℚ] p1HOverlap h :=
  IsLocalization.Away.liftAlgHom (x := h) (f := chart0ToHOverlap h)
    (chart0ToHOverlap_isUnit h)

/-- `ρ0` sends the image of `x : ℚ[λ]` to `chart0ToHOverlap x`. -/
theorem rho0_algebraMap (x : Polynomial ℚ) :
    rho0 h (algebraMap (Polynomial ℚ) (p1HChart0 h) x) = chart0ToHOverlap h x := by
  simp [rho0]

/-! ## `ρ1 : A1 → A01` -/

/-- `ρ1 : A1 → A01` of the `h`-refined cover: the localization `algebraMap P1Overlap A01`,
viewed as a `ℚ`-algebra map through the tower `ℚ → P1Overlap → A01`.  This is the same
map as `IsScalarTower.toAlgHom ℚ P1Overlap A01`. -/
noncomputable def rho1 : p1HChart1 →ₐ[ℚ] p1HOverlap h where
  toRingHom := algebraMap P1Overlap (p1HOverlap h)
  commutes' r := by
    have hc : ((algebraMap P1Overlap (p1HOverlap h)).comp
          (algebraMap ℚ p1HChart1)) = algebraMap ℚ (p1HOverlap h) := RingHom.ext_rat _ _
    exact RingHom.congr_fun hc r

/-- `rho1` is the structure map `P1Overlap → A01` on underlying elements. -/
theorem rho1_apply (x : p1HChart1) :
    rho1 h x = algebraMap P1Overlap (p1HOverlap h) x := by
  simp [rho1]

/-! ## The `h`-refined cover and its transition units -/

/-- The `h`-refined two-chart Cech cover of `P¹`: first chart `D(h)`, torus
`ℚ[λ,λ⁻¹]` as second chart, and `Away (h)` over the torus as overlap. -/
noncomputable def p1HRefinedCover : TwoChartCech.Cover ℚ where
  A0 := p1HChart0 h
  A1 := p1HChart1
  A01 := p1HOverlap h
  ρ0 := rho0 h
  ρ1 := rho1 h

theorem p1HRefinedCover_A0 : (p1HRefinedCover h).A0 = p1HChart0 h := rfl

theorem p1HRefinedCover_A1 : (p1HRefinedCover h).A1 = p1HChart1 := rfl

theorem p1HRefinedCover_A01 : (p1HRefinedCover h).A01 = p1HOverlap h := rfl

/-- The transition unit of `h^*O(1)` on the `h`-refined overlap: the image of `h` in
`A01`, which is a unit there by construction. -/
noncomputable def hUnitA01 : (p1HOverlap h)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := p1HOverlap h)
    (x := algebraMap (Polynomial ℚ) P1Overlap h)).unit

theorem hUnitA01_val : (hUnitA01 h : p1HOverlap h) =
    algebraMap P1Overlap (p1HOverlap h) (algebraMap (Polynomial ℚ) P1Overlap h) :=
  IsUnit.unit_spec (IsLocalization.Away.algebraMap_isUnit (S := p1HOverlap h)
    (x := algebraMap (Polynomial ℚ) P1Overlap h))

/-- The unit `λ` of the torus `P1Overlap`. -/
noncomputable def xUnitA1 : P1Overlapˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := P1Overlap)
    (x := (Polynomial.X : Polynomial ℚ))).unit

theorem xUnitA1_val : (xUnitA1 : P1Overlap) =
    algebraMap (Polynomial ℚ) P1Overlap (Polynomial.X : Polynomial ℚ) :=
  IsUnit.unit_spec (IsLocalization.Away.algebraMap_isUnit (S := P1Overlap)
    (x := (Polynomial.X : Polynomial ℚ)))

/-- The image of `λ` in `A01`. -/
noncomputable def xUnitA01 : (p1HOverlap h)ˣ :=
  Units.map (algebraMap P1Overlap (p1HOverlap h) : P1Overlap →* p1HOverlap h) xUnitA1

theorem xUnitA01_val : (xUnitA01 h : p1HOverlap h) =
    algebraMap P1Overlap (p1HOverlap h)
      (algebraMap (Polynomial ℚ) P1Overlap (Polynomial.X : Polynomial ℚ)) := by
  rw [xUnitA01, Units.coe_map, xUnitA1_val]
  rfl

/-- The transition unit of `O(d)` on the `h`-refined overlap: `λ^d = (λ⁻¹)⁻ᵈ`, the
`d`-th power of the image of the torus coordinate `λ`. -/
noncomputable def odUnit (d : ℕ) : (p1HOverlap h)ˣ := xUnitA01 h ^ d

theorem odUnit_val (d : ℕ) : (odUnit h d : p1HOverlap h) =
    (algebraMap P1Overlap (p1HOverlap h)
      (algebraMap (Polynomial ℚ) P1Overlap (Polynomial.X : Polynomial ℚ))) ^ d := by
  rw [odUnit, Units.val_pow_eq_pow_val, xUnitA01_val]

/-- The unit `h` of `A0` (chart `λ` restricted to `D(h)`), i.e. the first component of
the Cech coboundary trivializing `h^*O(1)`. -/
theorem h_isUnit_chart0 : IsUnit (algebraMap (Polynomial ℚ) (p1HChart0 h) h) :=
  IsLocalization.Away.algebraMap_isUnit (S := p1HChart0 h) (x := h)

noncomputable def a0 : (p1HChart0 h)ˣ := (h_isUnit_chart0 h).unit

theorem a0_val : (a0 h : p1HChart0 h) = algebraMap (Polynomial ℚ) (p1HChart0 h) h :=
  IsUnit.unit_spec (h_isUnit_chart0 h)

/-- The unit `λ^d` of the torus `P1Overlap`, i.e. the second component of the Cech
coboundary relating `O(d)` to `h^*O(1)`. -/
noncomputable def a1 (d : ℕ) : P1Overlapˣ := xUnitA1 ^ d

/-! ## The coboundary relation -/

/-- Value of `ρ0 (a0)` in `A01`: the image of `h`, i.e. the transition unit of
`h^*O(1)`. -/
theorem rho0_a0_val :
    (Units.map (rho0 h : p1HChart0 h →* p1HOverlap h) (a0 h) : p1HOverlap h) =
      algebraMap P1Overlap (p1HOverlap h) (algebraMap (Polynomial ℚ) P1Overlap h) := by
  rw [Units.coe_map, AlgHom.coe_toMonoidHom, a0_val, rho0_algebraMap,
    chart0ToHOverlap_apply]

/-- Value of `ρ1 (a1)` in `A01`: `λ^d`, i.e. the transition unit of `O(d)`. -/
theorem rho1_a1_val (d : ℕ) :
    (Units.map (rho1 h : p1HChart1 →* p1HOverlap h) (a1 d) : p1HOverlap h) =
      (algebraMap P1Overlap (p1HOverlap h)
        (algebraMap (Polynomial ℚ) P1Overlap (Polynomial.X : Polynomial ℚ))) ^ d := by
  rw [Units.coe_map, AlgHom.coe_toMonoidHom, a1, Units.val_pow_eq_pow_val, map_pow,
    xUnitA1_val, rho1_apply]

/-- **KEY COMPUTATION.**  On the `h`-refined cover the transition units of `h^*O(1)`
and of `O(d)` differ by the Cech coboundary `(a0, a1)`: since `h` is a unit of
`A0 = Away h` and `λ` is a unit of `A1 = P1Overlap`, both are trivialized and the
relation `hUnitA01 * ρ1 a1 = ρ0 a0 * odUnit` is the value identity
`h * λ^d = h * λ^d` in `A01`. -/
theorem transition_relation (d : ℕ) :
    hUnitA01 h * Units.map (rho1 h : p1HChart1 →* p1HOverlap h) (a1 d) =
      Units.map (rho0 h : p1HChart0 h →* p1HOverlap h) (a0 h) * odUnit h d := by
  ext
  rw [Units.val_mul, Units.val_mul, rho0_a0_val, hUnitA01_val, rho1_a1_val, odUnit_val]

/-! ## `h^*O(1) = O(natDegree h)` -/

/-- **B3**: the generic statement `h^*O(1) = O(natDegree h)` on `P¹` at the Cech level.
For a nonzero polynomial `h : ℚ[λ]` of degree `d`, the line bundle `h^*O(1)` -- given by
the transition unit `hUnitA01 h` (the image of `h` on the refined overlap) -- is
isomorphic to `O(d)`, whose transition unit is `odUnit h h.natDegree = λ^d`. -/
theorem b3_h_pullbackO1_iso (hh : h ≠ 0) :
    Nonempty (TwoChartCech.SectionsIso ((p1HRefinedCover h).lineBundle (odUnit h h.natDegree))
      ((p1HRefinedCover h).lineBundle (hUnitA01 h))) :=
  TwoChartCech.Cover.lineBundle_iso_of_mul (p1HRefinedCover h) (odUnit h h.natDegree)
    (hUnitA01 h) (a0 h) (a1 h.natDegree) (transition_relation h h.natDegree)

/-- The coboundary relation of `transition_relation`, solved for the reverse direction:
`odUnit` is also a coboundary multiple of `hUnitA01`. -/
theorem transition_relation_symm (d : ℕ) :
    odUnit h d * Units.map (rho1 h : p1HChart1 →* p1HOverlap h) (a1 d)⁻¹ =
      Units.map (rho0 h : p1HChart0 h →* p1HOverlap h) (a0 h)⁻¹ * hUnitA01 h := by
  rw [map_inv, map_inv]
  have hk := transition_relation h d
  have hk' : odUnit h d =
      (Units.map (rho0 h : p1HChart0 h →* p1HOverlap h) (a0 h))⁻¹ *
        (hUnitA01 h * Units.map (rho1 h : p1HChart1 →* p1HOverlap h) (a1 d)) := by
    calc odUnit h d
        = (Units.map (rho0 h : p1HChart0 h →* p1HOverlap h) (a0 h))⁻¹ *
            (Units.map (rho0 h : p1HChart0 h →* p1HOverlap h) (a0 h) * odUnit h d) := by
          rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = (Units.map (rho0 h : p1HChart0 h →* p1HOverlap h) (a0 h))⁻¹ *
            (hUnitA01 h * Units.map (rho1 h : p1HChart1 →* p1HOverlap h) (a1 d)) := by
          rw [← hk]
  rw [hk', mul_assoc, mul_assoc, mul_inv_cancel, mul_one]

/-- The symmetric form of `b3_h_pullbackO1_iso`: `O(natDegree h) ≅ h^*O(1)`. -/
theorem b3_h_pullbackO1_iso_symm (hh : h ≠ 0) :
    Nonempty (TwoChartCech.SectionsIso ((p1HRefinedCover h).lineBundle (hUnitA01 h))
      ((p1HRefinedCover h).lineBundle (odUnit h h.natDegree))) :=
  TwoChartCech.Cover.lineBundle_iso_of_mul (p1HRefinedCover h) (hUnitA01 h)
    (odUnit h h.natDegree) ((a0 h)⁻¹) ((a1 h.natDegree)⁻¹)
    (transition_relation_symm h h.natDegree)

/-! ## Axiom footprint -/

#print axioms p1HChart0
#print axioms p1HChart1
#print axioms p1HOverlap
#print axioms chart0ToHOverlap
#print axioms chart0ToHOverlap_apply
#print axioms chart0ToHOverlap_isUnit
#print axioms rho0
#print axioms rho0_algebraMap
#print axioms rho1
#print axioms rho1_apply
#print axioms p1HRefinedCover
#print axioms p1HRefinedCover_A0
#print axioms p1HRefinedCover_A1
#print axioms p1HRefinedCover_A01
#print axioms hUnitA01
#print axioms hUnitA01_val
#print axioms xUnitA1
#print axioms xUnitA1_val
#print axioms xUnitA01
#print axioms xUnitA01_val
#print axioms odUnit
#print axioms odUnit_val
#print axioms h_isUnit_chart0
#print axioms a0
#print axioms a0_val
#print axioms a1
#print axioms rho0_a0_val
#print axioms rho1_a1_val
#print axioms transition_relation
#print axioms transition_relation_symm
#print axioms b3_h_pullbackO1_iso
#print axioms b3_h_pullbackO1_iso_symm

end LeanFormal.IUT.XiFPaper.Mzk1G1B3HPullbackActual
