import Mathlib.Algebra.Ring.Int.Defs

/-- Superscript-two notation for squaring. -/
local notation:max x:max "²" => x ^ 2

/-- The square of a sum: `(a + b)² = a² + 2ab + b²` over the integers. -/
theorem square_of_sum (a b : ℤ) :
    (a + b)² = a² + 2 * a * b + b² := by
  calc (a + b)²
      -- write the square as a product
      = (a + b) * (a + b) := by rw [sq]
      -- distribute the right factor over the left sum
    _ = a * (a + b) + b * (a + b) := by rw [add_mul]
      -- distribute `a` and `b` over the remaining sums
    _ = (a * a + a * b) + (b * a + b * b) := by rw [mul_add, mul_add]
      -- commute `b * a` to `a * b` and regroup the two cross terms together
    _ = a * a + (a * b + a * b) + b * b := by rw [mul_comm b a, add_assoc, add_assoc, ← add_assoc (a * b)]
      -- fold the products into squares and the doubled cross term into `2 * a * b`
    _ = a² + 2 * a * b + b² := by rw [← sq, ← sq, ← two_mul, mul_assoc]
