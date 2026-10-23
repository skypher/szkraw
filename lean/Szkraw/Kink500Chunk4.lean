import Szkraw.Kink500Data350

open Szkraw.ColCheck

/-! Kernel check of one chunk of the windowed column of the `N = 500` one-kink example (P3, Section 9); the chunks
are assembled in `Kink500.lean`. -/

/-- Steps `350 → 500`: the corner `H_500(500)` is negative. -/
theorem Szkraw.kink500_chunk4 : (witer k5A k5B k5C 500 350 150 kink500ck350).2.2.2.headD 0 < 0 := by
  decide +kernel
