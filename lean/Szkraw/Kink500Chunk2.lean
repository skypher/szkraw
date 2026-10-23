import Szkraw.Kink500Data150
import Szkraw.Kink500Data250

open Szkraw.ColCheck

/-! Kernel check of one chunk of the windowed column of the `N = 500` one-kink example (P3, Section 9); the chunks
are assembled in `Kink500.lean`. -/

/-- Steps `150 → 250`. -/
theorem Szkraw.kink500_chunk2 : witer k5A k5B k5C 500 150 100 kink500ck150 = kink500ck250 := by
  decide +kernel
