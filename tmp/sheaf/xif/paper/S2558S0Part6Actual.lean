import Mathlib

noncomputable section
set_option maxHeartbeats 8000000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2558S0Part6Actual

/-- Coefficients 481..560 of the quotient S0. -/
def S0_6 : (ZMod 613)[X] := C 20 * X ^ 481 + C 409 * X ^ 482 + C 107 * X ^ 483 + C 89 * X ^ 484 + C 93 * X ^ 485 + C 55 * X ^ 486 + C 464 * X ^ 487 + C 427 * X ^ 488 + C 339 * X ^ 489 + C 194 * X ^ 490 + C 205 * X ^ 491 + C 482 * X ^ 492 + C 573 * X ^ 493 + C 129 * X ^ 494 + C 451 * X ^ 495 + C 334 * X ^ 496 + C 342 * X ^ 497 + C 113 * X ^ 498 + C 435 * X ^ 499 + C 163 * X ^ 500 + C 520 * X ^ 501 + C 103 * X ^ 502 + C 338 * X ^ 503 + C 450 * X ^ 504 + C 390 * X ^ 505 + C 362 * X ^ 506 + C 336 * X ^ 507 + C 83 * X ^ 508 + C 295 * X ^ 509 + C 359 * X ^ 510 + C 9 * X ^ 511 + C 314 * X ^ 512 + C 504 * X ^ 513 + C 433 * X ^ 514 + C 212 * X ^ 515 + C 419 * X ^ 516 + C 34 * X ^ 517 + C 307 * X ^ 518 + C 313 * X ^ 519 + C 11 * X ^ 520 + C 266 * X ^ 521 + C 242 * X ^ 522 + C 270 * X ^ 523 + C 605 * X ^ 524 + C 128 * X ^ 525 + C 362 * X ^ 526 + C 488 * X ^ 527 + C 253 * X ^ 528 + C 56 * X ^ 529 + C 327 * X ^ 530 + C 7 * X ^ 531 + C 301 * X ^ 532 + C 522 * X ^ 533 + C 430 * X ^ 534 + C 581 * X ^ 535 + C 546 * X ^ 536 + C 591 * X ^ 537 + C 329 * X ^ 538 + C 286 * X ^ 539 + C 446 * X ^ 540 + C 307 * X ^ 541 + C 96 * X ^ 542 + C 199 * X ^ 543 + C 565 * X ^ 544 + C 25 * X ^ 545 + C 589 * X ^ 546 + C 609 * X ^ 547 + C 241 * X ^ 548 + C 277 * X ^ 549 + C 499 * X ^ 550 + C 445 * X ^ 551 + C 297 * X ^ 552 + C 281 * X ^ 553 + C 378 * X ^ 554 + C 417 * X ^ 555 + C 168 * X ^ 556 + C 591 * X ^ 557 + C 56 * X ^ 558 + C 227 * X ^ 559 + C 272 * X ^ 560

theorem S0_6_natDegree_le : S0_6.natDegree ≤ 560 := by
  unfold S0_6
  compute_degree!

end LeanFormal.IUT.XiFPaper.S2558S0Part6Actual

end