import Szkraw.Kink500Data250
import Szkraw.Kink500Data350

open Szkraw.ColCheck

/-! Kernel check of one chunk of the windowed column of the `N = 500` one-kink example (P3, Section 9); the chunks
are assembled in `Kink500.lean`. -/

/-- Steps `250 → 350`. -/
theorem Szkraw.kink500_chunk3 : witer k5A k5B k5C 500 250 100 kink500ck250 = kink500ck350 := by
  decide +kernel
