import tmp.sheaf.xif.paper.S1977LevelwiseRealificationActual

set_option maxHeartbeats 2000000

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1949NonarchimedeanLogShellActual
open LeanFormal.IUT.XiFPaper.S1961LocalGlobalBridgeActual
open LeanFormal.IUT.XiFPaper.S1977LevelwiseRealificationActual
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual
open LeanFormal.IUT.NumberFieldFinitePlace

namespace S1977Consumer

-- 1. the constructed levelwise realification functional (on the multiplicative group)
#check @additiveNormLog
#check @levelwiseNormLog
#check @additiveNormLog_ofMul
#check @paperPreLogShell_eq_levelwiseNormLog_range
#check @paperLogShell_eq_levelwiseNormLog_image

-- 2. the actual unit group carries trivial norm-log data
#check @completionUnits_norm_eq_one
#check @realBridge_image_completionUnits

-- 3. the levelwise set equality is false, and no additive functional exists
#check @levelwise_equality_false
#check @levelwise_equality_false_datum
#check @no_additive_realification
#check @LevelwiseRealificationFunctional
#check @levelwiseRealificationFunctional_not_nonempty
#check @no_levelwise_realification_function
#check @additive_functional_trivial_on_preLogShell

-- 4. the sharp Q-span form (S1961)
#check @s1977_span_bridge_sharp

-- 5. actual uses: the obstruction rules out the proposed remaining object
example (v : FinitePrimePlace 2 7) :
    ¬ ∃ L : Completion (QPlace v) →+ ℝ,
        ∀ x ∈ (actualLocalLogShellDatum v).logShell, L x = realBridge v x :=
  no_additive_realification v

example (v : FinitePrimePlace 2 7) :
    realBridgeImage v ≠ ((paperLogShellDatum v).logShell : Set ℝ) :=
  levelwise_equality_false_datum v

example (v : FinitePrimePlace 2 7) : ¬ Nonempty (LevelwiseRealificationFunctional v) :=
  levelwiseRealificationFunctional_not_nonempty v

-- the additive functional on the multiplicative group evaluated at a unit
example (v : FinitePrimePlace 2 7) (u : (Completion (QPlace v))ˣ) :
    additiveNormLog v (Additive.ofMul u) = Real.log ‖(u : Completion (QPlace v))‖ :=
  additiveNormLog_ofMul v u

-- the levelwise identity for the reduced pre-log-shell, instantiated
example (v : FinitePrimePlace 2 7) :
    paperPreLogShell v =
      Set.range (fun u : (Completion (QPlace v))ˣ => (levelwiseNormLog v u).toAdd) :=
  paperPreLogShell_eq_levelwiseNormLog_range v

#print axioms no_additive_realification
#print axioms levelwise_equality_false
#print axioms paperLogShell_eq_levelwiseNormLog_image

end S1977Consumer
