import Mathlib

noncomputable section
set_option maxHeartbeats 8000000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2558S0Part4Actual

/-- Coefficients 321..400 of the quotient S0. -/
def S0_4 : (ZMod 613)[X] := C 232 * X ^ 321 + C 224 * X ^ 322 + C 245 * X ^ 323 + C 396 * X ^ 324 + C 170 * X ^ 325 + C 67 * X ^ 326 + C 261 * X ^ 327 + C 69 * X ^ 328 + C 73 * X ^ 329 + C 517 * X ^ 330 + C 329 * X ^ 331 + C 471 * X ^ 332 + C 491 * X ^ 333 + C 605 * X ^ 334 + C 375 * X ^ 335 + C 329 * X ^ 336 + C 602 * X ^ 337 + C 179 * X ^ 338 + C 462 * X ^ 339 + C 484 * X ^ 340 + C 375 * X ^ 341 + C 528 * X ^ 342 + C 404 * X ^ 343 + C 12 * X ^ 344 + C 353 * X ^ 345 + C 240 * X ^ 346 + C 374 * X ^ 347 + C 125 * X ^ 348 + C 491 * X ^ 349 + C 593 * X ^ 350 + C 453 * X ^ 351 + C 485 * X ^ 352 + C 533 * X ^ 353 + C 114 * X ^ 354 + C 494 * X ^ 355 + C 574 * X ^ 356 + C 285 * X ^ 357 + C 484 * X ^ 358 + C 20 * X ^ 359 + C 354 * X ^ 360 + C 16 * X ^ 361 + C 484 * X ^ 362 + C 452 * X ^ 363 + C 109 * X ^ 364 + C 450 * X ^ 365 + C 501 * X ^ 366 + C 467 * X ^ 367 + C 232 * X ^ 368 + C 21 * X ^ 369 + C 84 * X ^ 370 + C 18 * X ^ 371 + C 476 * X ^ 372 + C 529 * X ^ 373 + C 458 * X ^ 374 + C 265 * X ^ 375 + C 38 * X ^ 376 + C 366 * X ^ 377 + C 71 * X ^ 378 + C 605 * X ^ 379 + C 400 * X ^ 380 + C 511 * X ^ 381 + C 157 * X ^ 382 + C 109 * X ^ 383 + C 163 * X ^ 384 + C 22 * X ^ 385 + C 304 * X ^ 386 + C 75 * X ^ 387 + C 545 * X ^ 388 + C 448 * X ^ 389 + C 47 * X ^ 390 + C 7 * X ^ 391 + C 597 * X ^ 392 + C 75 * X ^ 393 + C 47 * X ^ 394 + C 204 * X ^ 395 + C 285 * X ^ 396 + C 241 * X ^ 397 + C 60 * X ^ 398 + C 597 * X ^ 399 + C 320 * X ^ 400

theorem S0_4_natDegree_le : S0_4.natDegree ≤ 400 := by
  unfold S0_4
  compute_degree!

end LeanFormal.IUT.XiFPaper.S2558S0Part4Actual

end