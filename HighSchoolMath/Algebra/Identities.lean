module

public import HighSchoolMath.Basic

/-!
# Algebraic Identities
-/

public section

namespace HighSchoolMath.Algebra

theorem twice_eq_two_mul (x : ℝ) :
    x + x = 2 * x := by
  ring

theorem add_zero_left (x : ℝ) : 0 + x = x := by
  exact zero_add x

theorem mul_one_right (x : ℝ) : x * 1 = x := by
  exact mul_one x

theorem sub_self_eq_zero (x : ℝ) : x - x = 0 := by
  simp

theorem add_sub_self_eq_left (x y : ℝ) :
    x + (y - y) = x := by
  simp

theorem two_mul_eq_add_self (x : ℝ) : 2 * x = x + x := by
  rw [twice_eq_two_mul]

theorem add_twice_eq (x y : ℝ) :
    x + (y + y) = x + 2 * y := by
  rw [twice_eq_two_mul]

theorem double_sum (x y : ℝ) :
    (x + y) + (x + y) = 2 * x + 2 * y := by
  calc
    (x+y) + (x+y) = 2 * (x+y) := by rw [twice_eq_two_mul]
    _ = 2 * x + 2 * y := by rw [mul_add]

theorem triple_eq_three_mul (x : ℝ) :
    (x + x) + x = 3 * x := by
  calc
    (x + x) + x = 2 * x + x := by rw [twice_eq_two_mul]
    _ = 2*x + 1*x := by rw [one_mul]
    _ = (2+1) * x := by rw [← add_mul]
    _ = 3 * x := by norm_num


end HighSchoolMath.Algebra
