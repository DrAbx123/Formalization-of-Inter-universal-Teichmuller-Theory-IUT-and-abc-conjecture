import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual

noncomputable section
set_option maxHeartbeats 16000000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2556Mod613Chain1ActualAdapted

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual

/-- Explicit quotient of X^613 by G. -/
def S0 : (ZMod 613)[X] := C 39 + C 281 * X + C 78 * X ^ 2 + C 265 * X ^ 3 + C 31 * X ^ 4 + C 121 * X ^ 5 + C 82 * X ^ 6 + C 150 * X ^ 7 + C 21 * X ^ 8 + C 336 * X ^ 9 + C 230 * X ^ 10 + C 554 * X ^ 11 + C 455 * X ^ 12 + C 168 * X ^ 13 + C 532 * X ^ 14 + C 32 * X ^ 15 + C 500 * X ^ 16 + C 163 * X ^ 17 + C 586 * X ^ 18 + C 118 * X ^ 19 + C 264 * X ^ 20 + C 560 * X ^ 21 + C 360 * X ^ 22 + C 309 * X ^ 23 + C 168 * X ^ 24 + C 601 * X ^ 25 + C 373 * X ^ 26 + C 288 * X ^ 27 + C 519 * X ^ 28 + C 73 * X ^ 29 + C 567 * X ^ 30 + C 465 * X ^ 31 + C 162 * X ^ 32 + C 370 * X ^ 33 + C 329 * X ^ 34 + C 331 * X ^ 35 + C 157 * X ^ 36 + C 337 * X ^ 37 + C 530 * X ^ 38 + C 236 * X ^ 39 + C 563 * X ^ 40 + C 120 * X ^ 41 + C 108 * X ^ 42 + C 117 * X ^ 43 + C 152 * X ^ 44 + C 368 * X ^ 45 + C 229 * X ^ 46 + C 448 * X ^ 47 + C 481 * X ^ 48 + C 152 * X ^ 49 + C 376 * X ^ 50 + C 161 * X ^ 51 + C 277 * X ^ 52 + C 224 * X ^ 53 + C 296 * X ^ 54 + C 525 * X ^ 55 + C 104 * X ^ 56 + C 92 * X ^ 57 + C 172 * X ^ 58 + C 219 * X ^ 59 + C 51 * X ^ 60 + C 530 * X ^ 61 + C 145 * X ^ 62 + C 520 * X ^ 63 + C 411 * X ^ 64 + C 489 * X ^ 65 + C 430 * X ^ 66 + C 373 * X ^ 67 + C 431 * X ^ 68 + C 240 * X ^ 69 + C 376 * X ^ 70 + C 185 * X ^ 71 + C 505 * X ^ 72 + C 200 * X ^ 73 + C 102 * X ^ 74 + C 60 * X ^ 75 + C 526 * X ^ 76 + C 47 * X ^ 77 + C 487 * X ^ 78 + C 295 * X ^ 79 + C 590 * X ^ 80 + C 240 * X ^ 81 + C 573 * X ^ 82 + C 118 * X ^ 83 + C 491 * X ^ 84 + C 112 * X ^ 85 + C 556 * X ^ 86 + C 112 * X ^ 87 + C 294 * X ^ 88 + C 564 * X ^ 89 + C 216 * X ^ 90 + C 245 * X ^ 91 + C 6 * X ^ 92 + C 208 * X ^ 93 + C 204 * X ^ 94 + C 477 * X ^ 95 + C 533 * X ^ 96 + C 72 * X ^ 97 + C 84 * X ^ 98 + C 238 * X ^ 99 + C 259 * X ^ 100 + C 506 * X ^ 101 + C 391 * X ^ 102 + C 459 * X ^ 103 + C 486 * X ^ 104 + C 280 * X ^ 105 + C 331 * X ^ 106 + C 499 * X ^ 107 + C 504 * X ^ 108 + C 68 * X ^ 109 + C 520 * X ^ 110 + C 436 * X ^ 111 + C 217 * X ^ 112 + C 226 * X ^ 113 + C 471 * X ^ 114 + C 604 * X ^ 115 + C 442 * X ^ 116 + C 217 * X ^ 117 + C 197 * X ^ 118 + C 553 * X ^ 119 + C 192 * X ^ 120 + C 83 * X ^ 121 + C 100 * X ^ 122 + C 319 * X ^ 123 + C 116 * X ^ 124 + C 256 * X ^ 125 + C 444 * X ^ 126 + C 168 * X ^ 127 + C 336 * X ^ 128 + C 383 * X ^ 129 + C 463 * X ^ 130 + C 115 * X ^ 131 + C 570 * X ^ 132 + C 516 * X ^ 133 + C 62 * X ^ 134 + C 29 * X ^ 135 + C 45 * X ^ 136 + C 127 * X ^ 137 + C 353 * X ^ 138 + C 128 * X ^ 139 + C 479 * X ^ 140 + C 218 * X ^ 141 + C 474 * X ^ 142 + C 570 * X ^ 143 + C 441 * X ^ 144 + C 530 * X ^ 145 + C 449 * X ^ 146 + C 26 * X ^ 147 + C 371 * X ^ 148 + C 345 * X ^ 149 + C 547 * X ^ 150 + C 485 * X ^ 151 + C 184 * X ^ 152 + C 501 * X ^ 153 + C 518 * X ^ 154 + C 612 * X ^ 155 + C 107 * X ^ 156 + C 253 * X ^ 157 + C 483 * X ^ 158 + C 21 * X ^ 159 + C 363 * X ^ 160 + C 122 * X ^ 161 + C 379 * X ^ 162 + C 221 * X ^ 163 + C 373 * X ^ 164 + C 182 * X ^ 165 + C 341 * X ^ 166 + C 406 * X ^ 167 + C 356 * X ^ 168 + C 395 * X ^ 169 + C 403 * X ^ 170 + C 278 * X ^ 171 + C 253 * X ^ 172 + C 24 * X ^ 173 + C 170 * X ^ 174 + C 438 * X ^ 175 + C 256 * X ^ 176 + C 341 * X ^ 177 + C 453 * X ^ 178 + C 198 * X ^ 179 + C 283 * X ^ 180 + C 343 * X ^ 181 + C 312 * X ^ 182 + C 33 * X ^ 183 + C 136 * X ^ 184 + C 427 * X ^ 185 + C 9 * X ^ 187 + C 154 * X ^ 188 + C 63 * X ^ 189 + C 80 * X ^ 190 + C 91 * X ^ 191 + C 405 * X ^ 192 + C 539 * X ^ 193 + C 603 * X ^ 194 + C 244 * X ^ 195 + C 609 * X ^ 196 + C 583 * X ^ 197 + C 384 * X ^ 198 + C 287 * X ^ 199 + C 265 * X ^ 200 + C 552 * X ^ 201 + C 9 * X ^ 202 + C 405 * X ^ 203 + C 75 * X ^ 204 + C 285 * X ^ 205 + C 62 * X ^ 206 + C 245 * X ^ 207 + C 93 * X ^ 208 + C 574 * X ^ 209 + C 205 * X ^ 210 + C 576 * X ^ 211 + C 490 * X ^ 212 + C 29 * X ^ 213 + C 420 * X ^ 214 + C 186 * X ^ 215 + C 247 * X ^ 216 + C 65 * X ^ 217 + C 405 * X ^ 218 + C 410 * X ^ 219 + C 193 * X ^ 220 + C 55 * X ^ 221 + C 544 * X ^ 222 + C 470 * X ^ 223 + C 276 * X ^ 224 + C 180 * X ^ 225 + C 604 * X ^ 226 + C 117 * X ^ 227 + C 314 * X ^ 228 + C 417 * X ^ 229 + C 477 * X ^ 230 + C 386 * X ^ 231 + C 369 * X ^ 232 + C 110 * X ^ 233 + C 172 * X ^ 234 + C 358 * X ^ 235 + C 512 * X ^ 236 + C 397 * X ^ 237 + C 431 * X ^ 238 + C 456 * X ^ 239 + C 455 * X ^ 240 + C 426 * X ^ 241 + C 595 * X ^ 242 + C 14 * X ^ 243 + C 2 * X ^ 244 + C 544 * X ^ 245 + C 133 * X ^ 246 + C 455 * X ^ 247 + C 556 * X ^ 248 + C 243 * X ^ 249 + C 558 * X ^ 250 + C 211 * X ^ 251 + C 226 * X ^ 252 + C 413 * X ^ 253 + C 406 * X ^ 254 + C 266 * X ^ 255 + C 460 * X ^ 256 + C 517 * X ^ 257 + C 36 * X ^ 258 + C 38 * X ^ 259 + C 212 * X ^ 260 + C 218 * X ^ 261 + C 552 * X ^ 262 + C 410 * X ^ 263 + C 198 * X ^ 264 + C 518 * X ^ 265 + C 373 * X ^ 266 + C 199 * X ^ 267 + C 205 * X ^ 268 + C 407 * X ^ 269 + C 144 * X ^ 270 + C 586 * X ^ 271 + C 69 * X ^ 272 + C 522 * X ^ 273 + C 216 * X ^ 274 + C 6 * X ^ 275 + C 320 * X ^ 276 + C 300 * X ^ 277 + C 417 * X ^ 278 + C 136 * X ^ 279 + C 289 * X ^ 280 + C 518 * X ^ 281 + C 469 * X ^ 282 + C 4 * X ^ 283 + C 6 * X ^ 284 + C 242 * X ^ 285 + C 7 * X ^ 286 + C 60 * X ^ 287 + C 141 * X ^ 288 + C 243 * X ^ 289 + C 10 * X ^ 290 + C 462 * X ^ 291 + C 439 * X ^ 292 + C 401 * X ^ 293 + C 479 * X ^ 294 + C 141 * X ^ 295 + C 47 * X ^ 296 + C 356 * X ^ 297 + C 191 * X ^ 298 + C 406 * X ^ 299 + C 545 * X ^ 300 + C 563 * X ^ 301 + C 301 * X ^ 302 + C 294 * X ^ 303 + C 476 * X ^ 304 + C 284 * X ^ 305 + C 202 * X ^ 306 + C 403 * X ^ 307 + C 209 * X ^ 308 + C 584 * X ^ 309 + C 33 * X ^ 310 + C 2 * X ^ 311 + C 280 * X ^ 312 + C 91 * X ^ 313 + C 131 * X ^ 314 + C 416 * X ^ 315 + C 303 * X ^ 316 + C 458 * X ^ 317 + C 211 * X ^ 318 + C 280 * X ^ 319 + C 400 * X ^ 320 + C 232 * X ^ 321 + C 224 * X ^ 322 + C 245 * X ^ 323 + C 396 * X ^ 324 + C 170 * X ^ 325 + C 67 * X ^ 326 + C 261 * X ^ 327 + C 69 * X ^ 328 + C 73 * X ^ 329 + C 517 * X ^ 330 + C 329 * X ^ 331 + C 471 * X ^ 332 + C 491 * X ^ 333 + C 605 * X ^ 334 + C 375 * X ^ 335 + C 329 * X ^ 336 + C 602 * X ^ 337 + C 179 * X ^ 338 + C 462 * X ^ 339 + C 484 * X ^ 340 + C 375 * X ^ 341 + C 528 * X ^ 342 + C 404 * X ^ 343 + C 12 * X ^ 344 + C 353 * X ^ 345 + C 240 * X ^ 346 + C 374 * X ^ 347 + C 125 * X ^ 348 + C 491 * X ^ 349 + C 593 * X ^ 350 + C 453 * X ^ 351 + C 485 * X ^ 352 + C 533 * X ^ 353 + C 114 * X ^ 354 + C 494 * X ^ 355 + C 574 * X ^ 356 + C 285 * X ^ 357 + C 484 * X ^ 358 + C 20 * X ^ 359 + C 354 * X ^ 360 + C 16 * X ^ 361 + C 484 * X ^ 362 + C 452 * X ^ 363 + C 109 * X ^ 364 + C 450 * X ^ 365 + C 501 * X ^ 366 + C 467 * X ^ 367 + C 232 * X ^ 368 + C 21 * X ^ 369 + C 84 * X ^ 370 + C 18 * X ^ 371 + C 476 * X ^ 372 + C 529 * X ^ 373 + C 458 * X ^ 374 + C 265 * X ^ 375 + C 38 * X ^ 376 + C 366 * X ^ 377 + C 71 * X ^ 378 + C 605 * X ^ 379 + C 400 * X ^ 380 + C 511 * X ^ 381 + C 157 * X ^ 382 + C 109 * X ^ 383 + C 163 * X ^ 384 + C 22 * X ^ 385 + C 304 * X ^ 386 + C 75 * X ^ 387 + C 545 * X ^ 388 + C 448 * X ^ 389 + C 47 * X ^ 390 + C 7 * X ^ 391 + C 597 * X ^ 392 + C 75 * X ^ 393 + C 47 * X ^ 394 + C 204 * X ^ 395 + C 285 * X ^ 396 + C 241 * X ^ 397 + C 60 * X ^ 398 + C 597 * X ^ 399 + C 320 * X ^ 400 + C 329 * X ^ 401 + C 248 * X ^ 402 + C 185 * X ^ 403 + C 308 * X ^ 404 + C 233 * X ^ 405 + C 120 * X ^ 406 + C 112 * X ^ 407 + C 137 * X ^ 408 + C 567 * X ^ 409 + C 473 * X ^ 410 + C 579 * X ^ 411 + C 18 * X ^ 412 + C 527 * X ^ 413 + C 351 * X ^ 414 + C 53 * X ^ 415 + C 47 * X ^ 416 + C 388 * X ^ 417 + C 507 * X ^ 418 + C 441 * X ^ 419 + C 473 * X ^ 420 + C 348 * X ^ 421 + C 18 * X ^ 422 + C 296 * X ^ 423 + C 131 * X ^ 424 + C 560 * X ^ 425 + C 11 * X ^ 426 + C 314 * X ^ 427 + C 386 * X ^ 428 + C 258 * X ^ 429 + C 376 * X ^ 430 + C 284 * X ^ 431 + C 481 * X ^ 432 + C 325 * X ^ 433 + C 336 * X ^ 434 + C 469 * X ^ 435 + C 59 * X ^ 436 + C 165 * X ^ 437 + C 234 * X ^ 438 + C 477 * X ^ 439 + C 599 * X ^ 440 + C 179 * X ^ 441 + C 372 * X ^ 442 + C 308 * X ^ 443 + C 180 * X ^ 444 + C 101 * X ^ 445 + C 437 * X ^ 446 + C 176 * X ^ 447 + C 282 * X ^ 448 + C 280 * X ^ 449 + C 182 * X ^ 450 + C 455 * X ^ 451 + C 504 * X ^ 452 + C 127 * X ^ 453 + C 332 * X ^ 454 + C 337 * X ^ 455 + C 518 * X ^ 456 + C 241 * X ^ 457 + C 507 * X ^ 458 + C 483 * X ^ 459 + C 308 * X ^ 460 + C 155 * X ^ 461 + C 450 * X ^ 462 + C 76 * X ^ 463 + C 529 * X ^ 464 + C 251 * X ^ 465 + C 320 * X ^ 466 + C 449 * X ^ 467 + C 376 * X ^ 468 + C 187 * X ^ 469 + C 262 * X ^ 470 + C 202 * X ^ 471 + C 408 * X ^ 472 + C 469 * X ^ 473 + C 210 * X ^ 474 + C 306 * X ^ 475 + C 172 * X ^ 476 + C 427 * X ^ 477 + C 261 * X ^ 478 + C 482 * X ^ 479 + C 172 * X ^ 480 + C 20 * X ^ 481 + C 409 * X ^ 482 + C 107 * X ^ 483 + C 89 * X ^ 484 + C 93 * X ^ 485 + C 55 * X ^ 486 + C 464 * X ^ 487 + C 427 * X ^ 488 + C 339 * X ^ 489 + C 194 * X ^ 490 + C 205 * X ^ 491 + C 482 * X ^ 492 + C 573 * X ^ 493 + C 129 * X ^ 494 + C 451 * X ^ 495 + C 334 * X ^ 496 + C 342 * X ^ 497 + C 113 * X ^ 498 + C 435 * X ^ 499 + C 163 * X ^ 500 + C 520 * X ^ 501 + C 103 * X ^ 502 + C 338 * X ^ 503 + C 450 * X ^ 504 + C 390 * X ^ 505 + C 362 * X ^ 506 + C 336 * X ^ 507 + C 83 * X ^ 508 + C 295 * X ^ 509 + C 359 * X ^ 510 + C 9 * X ^ 511 + C 314 * X ^ 512 + C 504 * X ^ 513 + C 433 * X ^ 514 + C 212 * X ^ 515 + C 419 * X ^ 516 + C 34 * X ^ 517 + C 307 * X ^ 518 + C 313 * X ^ 519 + C 11 * X ^ 520 + C 266 * X ^ 521 + C 242 * X ^ 522 + C 270 * X ^ 523 + C 605 * X ^ 524 + C 128 * X ^ 525 + C 362 * X ^ 526 + C 488 * X ^ 527 + C 253 * X ^ 528 + C 56 * X ^ 529 + C 327 * X ^ 530 + C 7 * X ^ 531 + C 301 * X ^ 532 + C 522 * X ^ 533 + C 430 * X ^ 534 + C 581 * X ^ 535 + C 546 * X ^ 536 + C 591 * X ^ 537 + C 329 * X ^ 538 + C 286 * X ^ 539 + C 446 * X ^ 540 + C 307 * X ^ 541 + C 96 * X ^ 542 + C 199 * X ^ 543 + C 565 * X ^ 544 + C 25 * X ^ 545 + C 589 * X ^ 546 + C 609 * X ^ 547 + C 241 * X ^ 548 + C 277 * X ^ 549 + C 499 * X ^ 550 + C 445 * X ^ 551 + C 297 * X ^ 552 + C 281 * X ^ 553 + C 378 * X ^ 554 + C 417 * X ^ 555 + C 168 * X ^ 556 + C 591 * X ^ 557 + C 56 * X ^ 558 + C 227 * X ^ 559 + C 272 * X ^ 560 + C 456 * X ^ 561 + C 591 * X ^ 562 + C 426 * X ^ 563 + C 254 * X ^ 564 + C 276 * X ^ 565 + C 43 * X ^ 566 + C 190 * X ^ 567 + C 417 * X ^ 568 + C 590 * X ^ 569 + C 124 * X ^ 570 + C 325 * X ^ 571 + C 549 * X ^ 572 + C 60 * X ^ 573 + C 559 * X ^ 574 + C 329 * X ^ 575 + C 366 * X ^ 576 + C 414 * X ^ 577 + C 19 * X ^ 578 + C 75 * X ^ 579 + C 281 * X ^ 580 + C 554 * X ^ 581 + C 540 * X ^ 582 + C 367 * X ^ 583 + C 380 * X ^ 584 + C 510 * X ^ 585 + C 494 * X ^ 586 + C 606 * X ^ 587 + C 509 * X ^ 588 + C 540 * X ^ 589 + C 349 * X ^ 590 + C 74 * X ^ 591 + C 345 * X ^ 592 + C 395 * X ^ 593 + C 161 * X ^ 594 + C 475 * X ^ 595 + C 171 * X ^ 596 + C 459 * X ^ 597 + C 424 * X ^ 598 + C 214 * X ^ 599 + C 341 * X ^ 600 + C 1 * X ^ 601

lemma chunk0 (n : ℕ) (hn0 : 0 ≤ n) (hn1 : n ≤ 80) :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n := by
  interval_cases n <;>
    (simp [S0, G, T1, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_one, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> norm_num)

lemma chunk1 (n : ℕ) (hn0 : 81 ≤ n) (hn1 : n ≤ 160) :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n := by
  interval_cases n <;>
    (simp [S0, G, T1, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_one, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> norm_num)

lemma chunk2 (n : ℕ) (hn0 : 161 ≤ n) (hn1 : n ≤ 240) :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n := by
  interval_cases n <;>
    (simp [S0, G, T1, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_one, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> norm_num)

lemma chunk3 (n : ℕ) (hn0 : 241 ≤ n) (hn1 : n ≤ 320) :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n := by
  interval_cases n <;>
    (simp [S0, G, T1, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_one, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> norm_num)

lemma chunk4 (n : ℕ) (hn0 : 321 ≤ n) (hn1 : n ≤ 400) :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n := by
  interval_cases n <;>
    (simp [S0, G, T1, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_one, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> norm_num)

lemma chunk5 (n : ℕ) (hn0 : 401 ≤ n) (hn1 : n ≤ 480) :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n := by
  interval_cases n <;>
    (simp [S0, G, T1, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_one, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> norm_num)

lemma chunk6 (n : ℕ) (hn0 : 481 ≤ n) (hn1 : n ≤ 560) :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n := by
  interval_cases n <;>
    (simp [S0, G, T1, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_one, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> norm_num)

lemma chunk7 (n : ℕ) (hn0 : 561 ≤ n) (hn1 : n ≤ 613) :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n := by
  interval_cases n <;>
    (simp [S0, G, T1, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_one, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> norm_num)

theorem chain1_identity :
    (X : (ZMod 613)[X]) ^ 613 - T1 = G * S0 := by
  ext n
  by_cases h0 : n ≤ 80
  · exact chunk0 n (by omega) h0
  have hn0 : 81 ≤ n := by omega
  by_cases h1 : n ≤ 160
  · exact chunk1 n hn0 h1
  have hn1 : 161 ≤ n := by omega
  by_cases h2 : n ≤ 240
  · exact chunk2 n hn1 h2
  have hn2 : 241 ≤ n := by omega
  by_cases h3 : n ≤ 320
  · exact chunk3 n hn2 h3
  have hn3 : 321 ≤ n := by omega
  by_cases h4 : n ≤ 400
  · exact chunk4 n hn3 h4
  have hn4 : 401 ≤ n := by omega
  by_cases h5 : n ≤ 480
  · exact chunk5 n hn4 h5
  have hn5 : 481 ≤ n := by omega
  by_cases h6 : n ≤ 560
  · exact chunk6 n hn5 h6
  have hn6 : 561 ≤ n := by omega
  by_cases h7 : n ≤ 613
  · exact chunk7 n hn6 h7
  · have hn : 614 ≤ n := by omega
    have hL : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : ((X : (ZMod 613)[X]) ^ 613 - T1).natDegree ≤ 613 := by
        unfold T1; compute_degree!
      omega
    have hR : (G * S0).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : (G * S0).natDegree ≤ 613 := by unfold G S0; compute_degree!
      omega
    rw [hL, hR]

theorem chain1_dvd : G ∣ (X : (ZMod 613)[X]) ^ 613 - T1 := ⟨S0, chain1_identity⟩

end LeanFormal.IUT.XiFPaper.S2556Mod613Chain1ActualAdapted

end