module

public import HighSchoolMath.Basic

/-!
# Algebraic Identities
-/

public section

namespace HighSchoolMath.Algebra

theorem twice_eq_two_mul {R : Type*} [Semiring R] (x : R) :
    x + x = 2 * x := by
  symm; exact two_mul x

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

theorem add_rearrange (x y z : ℝ) :
    (x + y) + z = (x + z) + y := by
  calc
    (x + y) + z = x + (y + z) := by rw [add_assoc]
    _ = x + (z + y) := by rw [add_comm y z]
    _ = (x + z) + y := by rw [add_assoc]

theorem factor_four_terms (a b x y : ℝ) :
    a * x + a * y + b * x + b * y =
      (a + b) * (x + y) := by
  calc
    a * x + a * y + b * x + b * y = (a * x + a * y) + (b * x + b * y) := by rw [add_assoc]
    _ = a * (x + y) + b * (x + y) := by rw [← mul_add, ← mul_add]
    _ = (a + b) * (x + y) := by rw [← add_mul]

theorem square_add (x y : ℝ) :
    (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

theorem square_sub (x y : ℝ) :
    (x - y) ^ 2 = x ^ 2 - 2 * x * y + y ^ 2 := by
  ring

theorem difference_of_squares (x y : ℝ) :
    x ^ 2 - y ^ 2 = (x - y) * (x + y) := by
  ring




end HighSchoolMath.Algebra
