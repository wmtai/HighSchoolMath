module

public import HighSchoolMath.Algebra.Identities

/-!
# Elementary Equation Rules

Basic equation transformations over the real numbers.
-/

public section

namespace HighSchoolMath.Algebra

theorem add_same_right (x y c : ℝ) (h : x = y) :
    x + c = y + c := by
  rw [h]

theorem cancel_add_right (x y c : ℝ) :
    x + c = y + c → x = y := by
  intro h
  apply add_right_cancel h



theorem double_eq_of_eq :
    ∀ x y : ℝ, x = y → 2 * x = 2 * y := by
  intro x y h
  rw [h]

theorem cancel_mul_left (a x y : ℝ) (ha : a ≠ 0) :
    a * x = a * y → x = y := by
  intro h
  apply mul_left_cancel₀ ha h

end HighSchoolMath.Algebra
