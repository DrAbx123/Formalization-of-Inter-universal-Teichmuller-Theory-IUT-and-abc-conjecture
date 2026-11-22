import Mathlib

noncomputable section
set_option maxHeartbeats 8000000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2558S0Part5Actual

/-- Coefficients 401..480 of the quotient S0. -/
def S0_5 : (ZMod 613)[X] := C 329 * X ^ 401 + C 248 * X ^ 402 + C 185 * X ^ 403 + C 308 * X ^ 404 + C 233 * X ^ 405 + C 120 * X ^ 406 + C 112 * X ^ 407 + C 137 * X ^ 408 + C 567 * X ^ 409 + C 473 * X ^ 410 + C 579 * X ^ 411 + C 18 * X ^ 412 + C 527 * X ^ 413 + C 351 * X ^ 414 + C 53 * X ^ 415 + C 47 * X ^ 416 + C 388 * X ^ 417 + C 507 * X ^ 418 + C 441 * X ^ 419 + C 473 * X ^ 420 + C 348 * X ^ 421 + C 18 * X ^ 422 + C 296 * X ^ 423 + C 131 * X ^ 424 + C 560 * X ^ 425 + C 11 * X ^ 426 + C 314 * X ^ 427 + C 386 * X ^ 428 + C 258 * X ^ 429 + C 376 * X ^ 430 + C 284 * X ^ 431 + C 481 * X ^ 432 + C 325 * X ^ 433 + C 336 * X ^ 434 + C 469 * X ^ 435 + C 59 * X ^ 436 + C 165 * X ^ 437 + C 234 * X ^ 438 + C 477 * X ^ 439 + C 599 * X ^ 440 + C 179 * X ^ 441 + C 372 * X ^ 442 + C 308 * X ^ 443 + C 180 * X ^ 444 + C 101 * X ^ 445 + C 437 * X ^ 446 + C 176 * X ^ 447 + C 282 * X ^ 448 + C 280 * X ^ 449 + C 182 * X ^ 450 + C 455 * X ^ 451 + C 504 * X ^ 452 + C 127 * X ^ 453 + C 332 * X ^ 454 + C 337 * X ^ 455 + C 518 * X ^ 456 + C 241 * X ^ 457 + C 507 * X ^ 458 + C 483 * X ^ 459 + C 308 * X ^ 460 + C 155 * X ^ 461 + C 450 * X ^ 462 + C 76 * X ^ 463 + C 529 * X ^ 464 + C 251 * X ^ 465 + C 320 * X ^ 466 + C 449 * X ^ 467 + C 376 * X ^ 468 + C 187 * X ^ 469 + C 262 * X ^ 470 + C 202 * X ^ 471 + C 408 * X ^ 472 + C 469 * X ^ 473 + C 210 * X ^ 474 + C 306 * X ^ 475 + C 172 * X ^ 476 + C 427 * X ^ 477 + C 261 * X ^ 478 + C 482 * X ^ 479 + C 172 * X ^ 480

theorem S0_5_natDegree_le : S0_5.natDegree ≤ 480 := by
  unfold S0_5
  compute_degree!

end LeanFormal.IUT.XiFPaper.S2558S0Part5Actual

end