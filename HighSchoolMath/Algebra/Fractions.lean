module

public import HighSchoolMath.Algebra.Identities

/-!
Fraction identities and cancellation over the real numbers.
-/

public section

namespace HighSchoolMath.Algebra

theorem cancel_fraction_factor (a b k : ℝ) (hk : k ≠ 0) :
    (a * k) / (b * k) = a / b := by
  exact mul_div_mul_right a b hk

theorem fraction_add (a b c d : ℝ)
    (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b + c / d = (a * d + c * b) / (b * d) := by
  field_simp [hb, hd]

theorem fraction_sub (a b c d : ℝ)
    (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b - c / d = (a * d - c * b) / (b * d) := by
  field_simp [hb, hd]

theorem fraction_eq_iff_cross_mul (a b c d : ℝ)
    (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b = c / d ↔ a * d = c * b := by
  constructor
  <;> intro h
  · field_simp [hb, hd] at h; simpa [mul_comm]
  · field_simp [hb, hd]; simpa [mul_comm] using h

theorem difference_of_squares_div (x y : ℝ)
    (hsum : x + y ≠ 0) :
    (x ^ 2 - y ^ 2) / (x + y) = x - y := by
  rw [difference_of_squares]
  field_simp [hsum]

end HighSchoolMath.Algebra
