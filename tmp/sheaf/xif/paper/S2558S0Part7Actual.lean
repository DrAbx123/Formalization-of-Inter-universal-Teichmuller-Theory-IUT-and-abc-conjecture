import Mathlib

noncomputable section
set_option maxHeartbeats 8000000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2558S0Part7Actual

/-- Coefficients 561..601 of the quotient S0. -/
def S0_7 : (ZMod 613)[X] := C 456 * X ^ 561 + C 591 * X ^ 562 + C 426 * X ^ 563 + C 254 * X ^ 564 + C 276 * X ^ 565 + C 43 * X ^ 566 + C 190 * X ^ 567 + C 417 * X ^ 568 + C 590 * X ^ 569 + C 124 * X ^ 570 + C 325 * X ^ 571 + C 549 * X ^ 572 + C 60 * X ^ 573 + C 559 * X ^ 574 + C 329 * X ^ 575 + C 366 * X ^ 576 + C 414 * X ^ 577 + C 19 * X ^ 578 + C 75 * X ^ 579 + C 281 * X ^ 580 + C 554 * X ^ 581 + C 540 * X ^ 582 + C 367 * X ^ 583 + C 380 * X ^ 584 + C 510 * X ^ 585 + C 494 * X ^ 586 + C 606 * X ^ 587 + C 509 * X ^ 588 + C 540 * X ^ 589 + C 349 * X ^ 590 + C 74 * X ^ 591 + C 345 * X ^ 592 + C 395 * X ^ 593 + C 161 * X ^ 594 + C 475 * X ^ 595 + C 171 * X ^ 596 + C 459 * X ^ 597 + C 424 * X ^ 598 + C 214 * X ^ 599 + C 341 * X ^ 600 + C 1 * X ^ 601

theorem S0_7_natDegree_le : S0_7.natDegree ≤ 601 := by
  unfold S0_7
  compute_degree!

end LeanFormal.IUT.XiFPaper.S2558S0Part7Actual

end