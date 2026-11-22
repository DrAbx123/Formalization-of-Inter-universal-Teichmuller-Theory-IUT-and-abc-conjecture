import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import tmp.sheaf.takkun.IutLean.Frobenioid.PrimeStripSystem
import tmp.sheaf.xif.paper.Mzk1HodgeToTakkunFieldsActual

/-! Mainline (A511-3): the Takkun `ThetaChain` (horizontal Theta-link chain of
mono-analytic cores) built from a REAL equivalence of two of our prime strips.  The
transition `0 -> 1` uses our `DPrimeStripEquiv` translated to the Takkun `DhPrimeStripEquiv`
(via its `isoG` field); all other transitions are reflexive.  This is a genuine chain
object, not an identity wrapper: the `0 -> 1` link is the given equivalence. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HodgeThetaChainActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT

universe u

variable {V : Type*}

/-- Our mono-analytic core `D` as a Takkun `Frobenioid.DhPrimeStrip` (only the Galois
  group family is kept). -/
def takkunDhOfOur (D : LeanFormal.IUT.DPrimeStrip V) :
    IUT.Frobenioid.DhPrimeStrip.{0} V where
  G := D.G

/-- Our `DPrimeStripEquiv` as an equivalence of the mono-analytic cores. -/
def takkunDhEquivOfOur {D D' : LeanFormal.IUT.DPrimeStrip V}
    (φ : LeanFormal.IUT.DPrimeStripEquiv D D') :
    IUT.Frobenioid.DhPrimeStripEquiv (takkunDhOfOur D) (takkunDhOfOur D') where
  isoG := φ.isoG

/-- The chain's core at level `n`: the source strip at `n = 0`, the target strip
  elsewhere. -/
def thetaChainCore (D D' : LeanFormal.IUT.DPrimeStrip V) (n : Int) :
    IUT.Frobenioid.DhPrimeStrip.{0} V :=
  if n = 0 then takkunDhOfOur D else takkunDhOfOur D'

@[simp] theorem thetaChainCore_zero (D D' : LeanFormal.IUT.DPrimeStrip V) :
    thetaChainCore D D' 0 = takkunDhOfOur D := by
  simp [thetaChainCore]

theorem thetaChainCore_ne (D D' : LeanFormal.IUT.DPrimeStrip V) {n : Int}
    (hn : n ≠ 0) : thetaChainCore D D' n = takkunDhOfOur D' := by
  simp [thetaChainCore, hn]

/-- The Theta-link at level `n`: the real equivalence `φ` at the transition
  `0 -> 1` (and its inverse at `-1 -> 0`), reflexive elsewhere. -/
def thetaChainLink (D D' : LeanFormal.IUT.DPrimeStrip V)
    (φ : LeanFormal.IUT.DPrimeStripEquiv D D') (n : Int) :
    IUT.Frobenioid.DhPrimeStripEquiv (thetaChainCore D D' n)
      (thetaChainCore D D' (n + 1)) := by
  by_cases h0 : n = 0
  · subst h0
    rw [thetaChainCore_zero, thetaChainCore_ne D D' (by norm_num : (0 : Int) + 1 ≠ 0)]
    exact takkunDhEquivOfOur φ
  · by_cases h1 : n + 1 = 0
    · have hn : n = -1 := by omega
      subst hn
      rw [thetaChainCore_ne D D' (by norm_num : (-1 : Int) ≠ 0), thetaChainCore_zero]
      exact takkunDhEquivOfOur φ.symm
    · rw [thetaChainCore_ne D D' h0, thetaChainCore_ne D D' h1]
      exact IUT.Frobenioid.DhPrimeStripEquiv.refl _

/-- The Takkun Theta-chain built from our prime-strip equivalence. -/
def takkunThetaChainOfEquiv (D D' : LeanFormal.IUT.DPrimeStrip V)
    (φ : LeanFormal.IUT.DPrimeStripEquiv D D') :
    IUT.Frobenioid.ThetaChain.{0} V where
  core := thetaChainCore D D'
  link := thetaChainLink D D' φ

@[simp] theorem takkunThetaChainOfEquiv_core_zero
    (D D' : LeanFormal.IUT.DPrimeStrip V)
    (φ : LeanFormal.IUT.DPrimeStripEquiv D D') :
    (takkunThetaChainOfEquiv D D' φ).core 0 = takkunDhOfOur D :=
  thetaChainCore_zero D D'

@[simp] theorem takkunThetaChainOfEquiv_core_one
    (D D' : LeanFormal.IUT.DPrimeStrip V)
    (φ : LeanFormal.IUT.DPrimeStripEquiv D D') :
    (takkunThetaChainOfEquiv D D' φ).core 1 = takkunDhOfOur D' :=
  thetaChainCore_ne D D' (by norm_num : (1 : Int) ≠ 0)

end

end LeanFormal.IUT.XiFPaper.Mzk1HodgeThetaChainActual