import Szkraw.Kink500Data150

open Szkraw.ColCheck

/-! Kernel check of one chunk of the windowed column of the `N = 500` one-kink example (P3, Section 9); the chunks
are assembled in `Kink500.lean`. -/

/-- Steps `0 → 150`. -/
theorem Szkraw.kink500_chunk1 : witer k5A k5B k5C 500 0 150 (winit 500) = kink500ck150 := by
  decide +kernel
