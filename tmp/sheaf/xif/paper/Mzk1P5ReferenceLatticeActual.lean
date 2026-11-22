/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1H2BasisConstructionActual
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic

/-! # P5 actual Haar reference lattice C_t -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P5ReferenceLatticeActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1H2BasisConstructionActual

universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)

/-- `ℤ_p`-module structure on the arithmetic packet tensor, restricted from `ℚ_p`. -/
noncomputable instance packetTensorZModModule [Algebra ℤ_[p] ℚ_[p]] :
    Module ℤ_[p] (ArithmeticPacketTensor places) :=
  Module.compHom _ (algebraMap ℤ_[p] ℚ_[p])

/-- The actual integral ring for the P5 reference lattice. -/
abbrev integralRing (p : ℕ) [Fact p.Prime] : Type := ℤ_[p]

/-- The reference lattice `C_t`: the `ℤ_p`-span of a chosen `ℚ_p`-basis of the
actual arithmetic packet tensor. -/
noncomputable def referenceLattice
    (B : Module.Basis (Fin (Module.finrank ℚ_[p] (ArithmeticPacketTensor places)))
      ℚ_[p] (ArithmeticPacketTensor places)) :
    Submodule ℤ_[p] (ArithmeticPacketTensor places) :=
  Submodule.span ℤ_[p] (Set.range B)

noncomputable def cLattice :
    Submodule ℤ_[p] (ArithmeticPacketTensor places) :=
  referenceLattice places (packetBasis places)

theorem cLattice_def :
    cLattice places = referenceLattice places (packetBasis places) := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P5ReferenceLatticeActual
