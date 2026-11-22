import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore
import LeanFormal.IUT.IUTI.HodgeTheater.ConcreteHodgeTheaterExample
import tmp.sheaf.takkun.IutLean.LogTheta.LogShell
import tmp.sheaf.takkun.IutLean.LogTheta.Lattice
import tmp.sheaf.takkun.IutLean.LogTheta.LatticeConcrete
import tmp.sheaf.takkun.IutLean.Arithmetic.RealHodgeTheater
import tmp.sheaf.xif.paper.Mzk1TakkunPrimeStripAdapterActual

/-! Mainline (A504): UNIFIED object skeleton as a REAL construction.

Built entirely from concrete objects (no parameter-wrapping fields):
* our core Hodge theater `LeanFormal.IUT.gaussianHodgeTheater l`;
* its Takkun `FhPrimeStrip` image via the A500 adapter;
* the Takkun real Hodge theater `IUT.Arithmetic.realHodgeTheater` (curve 11a3 model);
* a concrete log-theta lattice whose mono-analytic core is `IUT.Arithmetic.realDStrip.G`,
  whose unit group is `ℚ_[11]ˣ`, whose log shell is `ℤ_[11]`, and whose log-link is the
  p-adic valuation map `u ↦ v₁₁(u)` (a genuine additive homomorphism, constructed here in
  `modelLogMap` from `Padic.valuation_one/valuation_mul`);
* the log-link chain / Theta-link chain are the first column/row of that concrete lattice.

Imports are narrowed (no `Arithmetic/IntegrationTest` import: the log shell and valuation
log link are reconstructed locally from Mathlib's p-adic valuation API).  No sorry/axiom. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1UnifiedObjectSkeletonActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT

instance instFactPrimeEleven : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- The concrete log shell `ℤ_[11]` (the integral structure inside `ℚ_[11]`, compact additive). -/
def modelLogShell : IUT.LogTheta.LogShell.{0} := { carrier := ℤ_[11] }

/-- The p-adic valuation log map `u ↦ v₁₁(u)`: a genuine additive homomorphism
  `Additive ℚ_[11]ˣ →+ ℤ_[11]`. -/
def modelLogMap : Additive ℚ_[11]ˣ →+ ℤ_[11] where
  toFun u := ((((Additive.toMul u : ℚ_[11]ˣ) : ℚ_[11]).valuation : ℤ) : ℤ_[11])
  map_zero' := by
    change (((((1 : ℚ_[11]ˣ) : ℚ_[11])).valuation : ℤ) : ℤ_[11]) = 0
    rw [Units.val_one, Padic.valuation_one, Int.cast_zero]
  map_add' u v := by
    change ((((Additive.toMul u * Additive.toMul v : ℚ_[11]ˣ) : ℚ_[11]).valuation : ℤ)
        : ℤ_[11]) = _
    rw [Units.val_mul, Padic.valuation_mul (Units.ne_zero _) (Units.ne_zero _),
      Int.cast_add]

/-- The real log-link (valuation component) into the log shell. -/
def modelLogLink : IUT.LogTheta.LogLink ℚ_[11]ˣ modelLogShell where
  logMap := modelLogMap

/-- The valuation log map sends the q-parameter `11` to shell depth `1`. -/
theorem modelLogMap_qParam :
    modelLogMap (Additive.ofMul (Units.mk0 (11 : ℚ_[11]) (by norm_num))) = 1 := by
  change ((((11 : ℚ_[11])).valuation : ℤ) : ℤ_[11]) = 1
  rw [show ((11 : ℚ_[11])) = ((11 : ℕ) : ℚ_[11]) by norm_cast, Padic.valuation_p]
  norm_num

/-- The concrete log-theta lattice over the real arithmetic model: every grid point carries
  the real mono-analytic core `realDStrip.G`, the real unit group `ℚ_[11]ˣ`, the concrete log
  shell `ℤ_[11]`, and the valuation log-link. -/
def realConcreteLattice :
    IUT.LogTheta.LogThetaLatticeConcrete.{0} IUT.Arithmetic.RationalPlaces where
  core _ := { G := IUT.Arithmetic.realDStrip.G }
  thetaLink _ _ := IUT.Frobenioid.DhPrimeStripEquiv.refl _
  unit _ := ℚ_[11]ˣ
  shell _ := modelLogShell
  logLink _ _ := modelLogLink

/-- The unified object skeleton, all fields concrete. -/
structure UnifiedObjectSkeleton (l : PrimeGeFive) where
  hodge : LeanFormal.IUT.HodgeTheater l LeanFormal.IUT.RationalPrimePlace
  fh : IUT.Frobenioid.FhPrimeStrip.{0} LeanFormal.IUT.RationalPrimePlace
  theaterFull : IUT.HodgeTheater.Full
  concreteLattice : IUT.LogTheta.LogThetaLatticeConcrete.{0} IUT.Arithmetic.RationalPlaces
  lat : IUT.LogTheta.LogThetaLattice
  logChain : IUT.LogTheta.LogChain.{0}
  thetaChain : IUT.Frobenioid.ThetaChain.{0} IUT.Arithmetic.RationalPlaces
  shell : IUT.LogTheta.LogShell.{0}

/-- **The real model:** built from concrete objects; no field is a free parameter. -/
def unifiedSkeletonModel (l : PrimeGeFive) : UnifiedObjectSkeleton l where
  hodge := gaussianHodgeTheater l
  fh := Mzk1TakkunPrimeStripAdapterActual.takkunFhOfOur (gaussianHodgeTheater l).primeStrip
  theaterFull := IUT.Arithmetic.realHodgeTheater
  concreteLattice := realConcreteLattice
  lat := { HT := fun _ => IUT.Arithmetic.realHodgeTheater }
  logChain := realConcreteLattice.logColumn 0
  thetaChain := realConcreteLattice.thetaRow 0
  shell := modelLogShell

theorem unifiedSkeletonModel_hodge (l : PrimeGeFive) :
    (unifiedSkeletonModel l).hodge = gaussianHodgeTheater l := rfl

theorem unifiedSkeletonModel_fh (l : PrimeGeFive) :
    (unifiedSkeletonModel l).fh =
      Mzk1TakkunPrimeStripAdapterActual.takkunFhOfOur (gaussianHodgeTheater l).primeStrip := rfl

theorem unifiedSkeletonModel_theaterFull (l : PrimeGeFive) :
    (unifiedSkeletonModel l).theaterFull = IUT.Arithmetic.realHodgeTheater := rfl

theorem unifiedSkeletonModel_shell (l : PrimeGeFive) :
    (unifiedSkeletonModel l).shell = modelLogShell := rfl

def unifiedSkeletonModel_shell_carrier_constructed (l : PrimeGeFive) :
    AddCommGroup (unifiedSkeletonModel l).shell.carrier := inferInstance

theorem unifiedSkeletonModel_logChain_shell (l : PrimeGeFive) (m : Int) :
    (unifiedSkeletonModel l).logChain.shell m = modelLogShell := rfl

theorem unifiedSkeletonModel_thetaChain_core (l : PrimeGeFive) (n : Int) :
    (unifiedSkeletonModel l).thetaChain.core n =
      ({ G := IUT.Arithmetic.realDStrip.G } :
        IUT.Frobenioid.DhPrimeStrip IUT.Arithmetic.RationalPlaces) := rfl

theorem unifiedSkeletonModel_logLink_one (l : PrimeGeFive) :
    (modelLogLink).logMap (Additive.ofMul (1 : ℚ_[11]ˣ)) = 0 :=
  IUT.LogTheta.LogLink.logMap_one modelLogLink

theorem unifiedSkeletonModel_logMap_qParam (l : PrimeGeFive) :
    modelLogMap (Additive.ofMul (Units.mk0 (11 : ℚ_[11]) (by norm_num))) = 1 :=
  modelLogMap_qParam

theorem unifiedSkeletonModel_nonempty (l : PrimeGeFive) :
    Nonempty (UnifiedObjectSkeleton l) :=
  ⟨unifiedSkeletonModel l⟩

end

end LeanFormal.IUT.XiFPaper.Mzk1UnifiedObjectSkeletonActual