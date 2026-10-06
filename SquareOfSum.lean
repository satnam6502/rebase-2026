import Mathlib

/-- Superscript-two notation for squaring. -/
local notation:max x:max "²" => x ^ 2

/-- The square of a sum: `(a + b)² = a² + 2ab + b²` over the integers. -/
theorem square_of_sum (a b : ℤ) :
    (a + b)² = a² + 2 * a * b + b² := by sorry
