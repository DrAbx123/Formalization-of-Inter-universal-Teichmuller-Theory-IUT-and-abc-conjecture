import Mathlib

noncomputable section
set_option maxHeartbeats 8000000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2558S0Part3Actual

/-- Coefficients 241..320 of the quotient S0. -/
def S0_3 : (ZMod 613)[X] := C 426 * X ^ 241 + C 595 * X ^ 242 + C 14 * X ^ 243 + C 2 * X ^ 244 + C 544 * X ^ 245 + C 133 * X ^ 246 + C 455 * X ^ 247 + C 556 * X ^ 248 + C 243 * X ^ 249 + C 558 * X ^ 250 + C 211 * X ^ 251 + C 226 * X ^ 252 + C 413 * X ^ 253 + C 406 * X ^ 254 + C 266 * X ^ 255 + C 460 * X ^ 256 + C 517 * X ^ 257 + C 36 * X ^ 258 + C 38 * X ^ 259 + C 212 * X ^ 260 + C 218 * X ^ 261 + C 552 * X ^ 262 + C 410 * X ^ 263 + C 198 * X ^ 264 + C 518 * X ^ 265 + C 373 * X ^ 266 + C 199 * X ^ 267 + C 205 * X ^ 268 + C 407 * X ^ 269 + C 144 * X ^ 270 + C 586 * X ^ 271 + C 69 * X ^ 272 + C 522 * X ^ 273 + C 216 * X ^ 274 + C 6 * X ^ 275 + C 320 * X ^ 276 + C 300 * X ^ 277 + C 417 * X ^ 278 + C 136 * X ^ 279 + C 289 * X ^ 280 + C 518 * X ^ 281 + C 469 * X ^ 282 + C 4 * X ^ 283 + C 6 * X ^ 284 + C 242 * X ^ 285 + C 7 * X ^ 286 + C 60 * X ^ 287 + C 141 * X ^ 288 + C 243 * X ^ 289 + C 10 * X ^ 290 + C 462 * X ^ 291 + C 439 * X ^ 292 + C 401 * X ^ 293 + C 479 * X ^ 294 + C 141 * X ^ 295 + C 47 * X ^ 296 + C 356 * X ^ 297 + C 191 * X ^ 298 + C 406 * X ^ 299 + C 545 * X ^ 300 + C 563 * X ^ 301 + C 301 * X ^ 302 + C 294 * X ^ 303 + C 476 * X ^ 304 + C 284 * X ^ 305 + C 202 * X ^ 306 + C 403 * X ^ 307 + C 209 * X ^ 308 + C 584 * X ^ 309 + C 33 * X ^ 310 + C 2 * X ^ 311 + C 280 * X ^ 312 + C 91 * X ^ 313 + C 131 * X ^ 314 + C 416 * X ^ 315 + C 303 * X ^ 316 + C 458 * X ^ 317 + C 211 * X ^ 318 + C 280 * X ^ 319 + C 400 * X ^ 320

theorem S0_3_natDegree_le : S0_3.natDegree ≤ 320 := by
  unfold S0_3
  compute_degree!

end LeanFormal.IUT.XiFPaper.S2558S0Part3Actual

end