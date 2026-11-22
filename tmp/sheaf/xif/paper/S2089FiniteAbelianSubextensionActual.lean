/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import tmp.sheaf.xif.paper.S2056MaxAbelianBridge

/-!
# S2089: the reverse inclusion for `PadicField.maxAbelian = L^ab`

S2056 reduced the missing bridge between LANA's local-CFT field

  `PadicField.maxAbelian (localField p U) (AlgebraicClosure ℚ_[p])`

and S2027's infinite-Galois construction

  `maximalAbelianExtension p U
     = fixedField ((commutator Gal(Qbar_p/L)).topologicalClosure)`

to one statement, `S2056MaxAbelianBridge.FiniteAbelianSubextension`:

  every `x ∈ maximalAbelianExtension p U` lies in **some** finite abelian
  subextension `L : PadicField.AbFin (localField p U) (AlgebraicClosure ℚ_[p])`.

This file proves that statement unconditionally and derives the equality and
the induced Galois-group equivalence.

## Proof

Given `x ∈ L^ab = fixedField H`, where `H = closure [G,G]`, `G = Gal(Qbar_p/L)`:

* `L₀ = L(x)` is finite over `L`, because `x` is algebraic (hence integral)
  over `L` (an element of `Qbar_p`);
* `M = normalClosure L L₀ Qbar_p` is finite and Galois over `L`
  (`normalClosure.is_finiteDimensional`, `IsGalois.normalClosure`);
* `L^ab` is normal over `L`: `H = (L^ab).fixingSubgroup` is normal, so
  `IsGalois L L^ab` by `InfiniteGalois.normal_iff_isGalois`; hence
  `normalClosure_le_iff_of_normal` gives `M ≤ L^ab`;
* `Gal(L^ab/L)` is commutative by S2027
  (`galoisGroupMaximalAbelian_commGroup`), so `IsAbelianGalois L L^ab`;
  the inclusion `M → L^ab` then makes `M/L` abelian Galois
  (`IsAbelianGalois.of_algHom`).

Thus `M` is the required finite abelian subextension containing `x`, and
`x ∈ PadicField.maxAbelian` by `PadicField.mem_maxAbelian_iff`.  The reverse
inclusion is S2056's `maxAbelian_le_maximalAbelianExtension`; antisymmetry
gives the equality.  Finally `AlgEquiv.autCongr` of the induced field
equivalence gives the Galois-group equivalence.

The construction uses only the infinite Galois correspondence of S2027; no
local class field theory input and no new axiom is used.  The `#print axioms`
probes below should contain only `propext`, `Classical.choice`, `Quot.sound`.
-/

noncomputable section
set_option maxHeartbeats 2000000
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2056MaxAbelianBridge
open IntermediateField

namespace LeanFormal.IUT.XiFPaper.S2089FiniteAbelianSubextensionActual

variable {p : Nat} [Fact (Nat.Prime p)]
variable (U : LeanFormal.IUT.XiFPaper.S2017VerlagerungActual.Index p)

local notation "E" => localField p U
local notation "Ω" => AlgebraicClosure ℚ_[p]

/-! ## The finite abelian subextension through a point of `L^ab` -/

/-- **The exact missing statement of S2056 is true**: every element of the
maximal abelian extension lies in a finite abelian subextension. -/
theorem finiteAbelianSubextension : FiniteAbelianSubextension U := by
  intro x
  -- `L₀ = E(x)` is finite over `E`.
  let L₀ : IntermediateField E Ω := IntermediateField.adjoin E {(x : Ω)}
  have hxint : IsIntegral E (x : Ω) := by
    have h1 : IsIntegral ℚ_[p] (x : Ω) := Algebra.IsIntegral.isIntegral _
    exact h1.tower_top
  haveI hL₀fd : FiniteDimensional E L₀ := IntermediateField.adjoin.finiteDimensional hxint
  -- `L = normalClosure E L₀ Ω` is finite and Galois over `E`.
  let L : IntermediateField E Ω := IntermediateField.normalClosure E L₀ Ω
  haveI hLfd : FiniteDimensional E L := normalClosure.is_finiteDimensional E L₀ Ω
  have hL₀M : L₀ ≤ maximalAbelianExtension p U :=
    IntermediateField.adjoin_simple_le_iff.mpr x.2
  -- `L^ab` is Galois (hence normal) over `E`.
  haveI hGalM : IsGalois E (maximalAbelianExtension p U) := by
    haveI hfix : (maximalAbelianExtension p U).fixingSubgroup.Normal := by
      rw [fixingSubgroup_maximalAbelianExtension p U]
      exact commutatorClosed_normal p U
    exact (InfiniteGalois.normal_iff_isGalois (maximalAbelianExtension p U)).mp hfix
  haveI hNormalM : Normal E (maximalAbelianExtension p U) := IsGalois.to_normal
  -- Normality of `L^ab / E` puts the normal closure inside `L^ab`.
  have hLM : L ≤ maximalAbelianExtension p U :=
    IntermediateField.normalClosure_le_iff_of_normal.mpr hL₀M
  haveI hGalL : IsGalois E L := inferInstance
  -- `Gal(L^ab/E)` is commutative, and `Gal(L/E)` is a quotient of it.
  haveI hAbM : IsAbelianGalois E (maximalAbelianExtension p U) :=
    { toIsGalois := hGalM
      toIsMulCommutative := ⟨⟨fun σ τ => mul_comm σ τ⟩⟩ }
  haveI hAbL : IsAbelianGalois E L :=
    IsAbelianGalois.of_algHom (IntermediateField.inclusion hLM)
  -- `x ∈ L₀ ≤ L`, so `L` is the desired `AbFin`.
  exact ⟨⟨L, hLfd, hAbL⟩,
    IntermediateField.le_normalClosure L₀ (IntermediateField.mem_adjoin_simple_self E (x : Ω))⟩

/-! ## The equality of the two maximal abelian extensions -/

/-- The reverse inclusion of S2056's `maxAbelian_le_maximalAbelianExtension`. -/
theorem maximalAbelianExtension_le_maxAbelian :
    maximalAbelianExtension p U ≤ PadicField.maxAbelian E Ω := by
  intro x hx
  rw [PadicField.mem_maxAbelian_iff]
  exact finiteAbelianSubextension U ⟨x, hx⟩

/-- **`PadicField.maxAbelian` is S2027's `maximalAbelianExtension`.**  This is
the exact missing M2a bridge recorded in the S2050/S2056 reports. -/
theorem maxAbelian_eq_maximalAbelianExtension :
    PadicField.maxAbelian E Ω = maximalAbelianExtension p U :=
  le_antisymm (maxAbelian_le_maximalAbelianExtension U)
    (maximalAbelianExtension_le_maxAbelian U)

/-- Set-theoretic form of the equality: `L^ab` is the union of the finite
abelian subextensions. -/
theorem mem_maximalAbelianExtension_iff {x : Ω} :
    x ∈ maximalAbelianExtension p U ↔ ∃ L : PadicField.AbFin E Ω, x ∈ L.1 := by
  rw [← maxAbelian_eq_maximalAbelianExtension U]
  exact PadicField.mem_maxAbelian_iff

/-- `L^ab` as the directed supremum of the finite abelian subextensions. -/
theorem maximalAbelianExtension_eq_iSup :
    maximalAbelianExtension p U =
      ⨆ L : PadicField.AbFin E Ω, (L.1 : IntermediateField E Ω) := by
  rw [← maxAbelian_eq_maximalAbelianExtension U]
  rfl

/-! ## The induced field and Galois-group equivalences -/

/-- The canonical `E`-algebra equivalence between the two realisations of the
maximal abelian extension, induced by the field equality. -/
noncomputable def maxAbelianEquivMaximalAbelianExtension :
    PadicField.maxAbelian E Ω ≃ₐ[E] maximalAbelianExtension p U :=
  IntermediateField.equivOfEq (maxAbelian_eq_maximalAbelianExtension U)

/-- **The induced Galois-group equivalence**

  `Gal(maxAbelian / L) ≃* Gal(maximalAbelianExtension / L)`.

This is the second half of the S2050 M2a bridge: it transports LANA's Artin map
`PadicField.artin : L^× →* Gal(maxAbelian / L)` to a map into S2027's group
`Gal(L^ab / L)`. -/
noncomputable def galoisGroupEquiv :
    Gal(↥(PadicField.maxAbelian E Ω) / E) ≃*
      Gal(↥(maximalAbelianExtension p U) / E) :=
  AlgEquiv.autCongr (maxAbelianEquivMaximalAbelianExtension U)

/-- The induced field equivalence is the identity on underlying elements. -/
@[simp]
theorem maxAbelianEquivMaximalAbelianExtension_apply
    (y : PadicField.maxAbelian E Ω) :
    ((maxAbelianEquivMaximalAbelianExtension U y : maximalAbelianExtension p U) : Ω) = (y : Ω) :=
  rfl

/-- The Galois-group equivalence acts by conjugating with the field
equivalence. -/
theorem galoisGroupEquiv_apply (σ : Gal(↥(PadicField.maxAbelian E Ω) / E))
    (y : maximalAbelianExtension p U) :
    (galoisGroupEquiv U σ) y =
      maxAbelianEquivMaximalAbelianExtension U
        (σ ((maxAbelianEquivMaximalAbelianExtension U).symm y)) :=
  rfl

end LeanFormal.IUT.XiFPaper.S2089FiniteAbelianSubextensionActual

#print axioms LeanFormal.IUT.XiFPaper.S2089FiniteAbelianSubextensionActual.finiteAbelianSubextension
#print axioms LeanFormal.IUT.XiFPaper.S2089FiniteAbelianSubextensionActual.maximalAbelianExtension_le_maxAbelian
#print axioms LeanFormal.IUT.XiFPaper.S2089FiniteAbelianSubextensionActual.maxAbelian_eq_maximalAbelianExtension
#print axioms LeanFormal.IUT.XiFPaper.S2089FiniteAbelianSubextensionActual.mem_maximalAbelianExtension_iff
#print axioms LeanFormal.IUT.XiFPaper.S2089FiniteAbelianSubextensionActual.maximalAbelianExtension_eq_iSup
#print axioms LeanFormal.IUT.XiFPaper.S2089FiniteAbelianSubextensionActual.maxAbelianEquivMaximalAbelianExtension
#print axioms LeanFormal.IUT.XiFPaper.S2089FiniteAbelianSubextensionActual.galoisGroupEquiv
#print axioms LeanFormal.IUT.XiFPaper.S2089FiniteAbelianSubextensionActual.maxAbelianEquivMaximalAbelianExtension_apply
#print axioms LeanFormal.IUT.XiFPaper.S2089FiniteAbelianSubextensionActual.galoisGroupEquiv_apply
