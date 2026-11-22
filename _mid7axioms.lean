import tmp.sheaf.xif.paper.S2564Chain1Mid7Actual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2564Chain1Mid7Check

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual
open LeanFormal.IUT.XiFPaper.S2564Chain1Mid7Actual

/-! Target lock: the range statement has exactly the requested shape. -/
example : ∀ n : ℕ, 481 ≤ n → n ≤ 560 →
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n :=
  fun n h1 h2 => chain1_coeff_mid n h1 h2

example : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 481 = (G * S0).coeff 481 :=
  chain1_coeff_481

example : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 560 = (G * S0).coeff 560 :=
  chain1_coeff_560

#print axioms chain1_coeff_mid
#print axioms chain1_coeff_481
#print axioms chain1_coeff_482
#print axioms chain1_coeff_483
#print axioms chain1_coeff_484
#print axioms chain1_coeff_485
#print axioms chain1_coeff_486
#print axioms chain1_coeff_487
#print axioms chain1_coeff_488
#print axioms chain1_coeff_489
#print axioms chain1_coeff_490
#print axioms chain1_coeff_491
#print axioms chain1_coeff_492
#print axioms chain1_coeff_493
#print axioms chain1_coeff_494
#print axioms chain1_coeff_495
#print axioms chain1_coeff_496
#print axioms chain1_coeff_497
#print axioms chain1_coeff_498
#print axioms chain1_coeff_499
#print axioms chain1_coeff_500
#print axioms chain1_coeff_501
#print axioms chain1_coeff_502
#print axioms chain1_coeff_503
#print axioms chain1_coeff_504
#print axioms chain1_coeff_505
#print axioms chain1_coeff_506
#print axioms chain1_coeff_507
#print axioms chain1_coeff_508
#print axioms chain1_coeff_509
#print axioms chain1_coeff_510
#print axioms chain1_coeff_511
#print axioms chain1_coeff_512
#print axioms chain1_coeff_513
#print axioms chain1_coeff_514
#print axioms chain1_coeff_515
#print axioms chain1_coeff_516
#print axioms chain1_coeff_517
#print axioms chain1_coeff_518
#print axioms chain1_coeff_519
#print axioms chain1_coeff_520
#print axioms chain1_coeff_521
#print axioms chain1_coeff_522
#print axioms chain1_coeff_523
#print axioms chain1_coeff_524
#print axioms chain1_coeff_525
#print axioms chain1_coeff_526
#print axioms chain1_coeff_527
#print axioms chain1_coeff_528
#print axioms chain1_coeff_529
#print axioms chain1_coeff_530
#print axioms chain1_coeff_531
#print axioms chain1_coeff_532
#print axioms chain1_coeff_533
#print axioms chain1_coeff_534
#print axioms chain1_coeff_535
#print axioms chain1_coeff_536
#print axioms chain1_coeff_537
#print axioms chain1_coeff_538
#print axioms chain1_coeff_539
#print axioms chain1_coeff_540
#print axioms chain1_coeff_541
#print axioms chain1_coeff_542
#print axioms chain1_coeff_543
#print axioms chain1_coeff_544
#print axioms chain1_coeff_545
#print axioms chain1_coeff_546
#print axioms chain1_coeff_547
#print axioms chain1_coeff_548
#print axioms chain1_coeff_549
#print axioms chain1_coeff_550
#print axioms chain1_coeff_551
#print axioms chain1_coeff_552
#print axioms chain1_coeff_553
#print axioms chain1_coeff_554
#print axioms chain1_coeff_555
#print axioms chain1_coeff_556
#print axioms chain1_coeff_557
#print axioms chain1_coeff_558
#print axioms chain1_coeff_559
#print axioms chain1_coeff_560
#print axioms S0_coeff_block5
#print axioms S0_coeff_block6
#print axioms S0_coeff_469
#print axioms S0_coeff_560

end LeanFormal.IUT.XiFPaper.S2564Chain1Mid7Check

end
