module

import HighSchoolMath

/-!
# Library Usage Examples
-/

example : (8 : ℝ) + 7 = 15 := by
  exact HighSchoolMath.addition_check

example (x : ℝ) : x + x = 2 * x := by
  exact HighSchoolMath.Algebra.twice_eq_two_mul x

example : (5 : ℝ) + 5 = 2 * 5 := by
  exact HighSchoolMath.Algebra.twice_eq_two_mul 5

-- 1–2: Subtraction in different number systems.

example : (4 : ℕ) - 9 = 0 := by
  norm_num

example : (4 : ℤ) - 9 = -5 := by
  norm_num

-- 3–6: Division in all four number systems.

example : (9 : ℕ) / 4 = 2 := by
  norm_num

example : (9 : ℤ) / 4 = 2 := by
  norm_num

example : (9 : ℚ) / 4 = 2 + 1 / 4 := by
  norm_num

example : (9 : ℝ) / 4 = 2 + 1 / 4 := by
  norm_num

-- 7–8: Convert after subtraction versus before subtraction.

example : ((4 - 9 : ℕ) : ℤ) = 0 := by
  norm_num

example : ((4 : ℕ) : ℤ) - 9 = -5 := by
  norm_num

-- 9–10: Convert after division versus before division.

example : ((9 / 4 : ℕ) : ℚ) = 2 := by
  norm_num

example : ((9 : ℕ) : ℚ) / 4 = 2 + 1 / 4 := by
  norm_num


example : (12 + 1 : ℕ) - 1 = 12 := by
  exact HighSchoolMath.successor_sub_one 12

example (x : ℝ) : 0 + x = x := by
  exact HighSchoolMath.Algebra.add_zero_left x

example : (7 : ℝ) * 1 = 7 := by
  exact HighSchoolMath.Algebra.mul_one_right 7

example (t : ℝ) : t - t = 0 := by
  exact HighSchoolMath.Algebra.sub_self_eq_zero t

example (a b : ℝ) : a + (b - b) = a := by
  exact HighSchoolMath.Algebra.add_sub_self_eq_left a b


example : (2 : ℝ) * 5 = 5 + 5 := by
  exact HighSchoolMath.Algebra.two_mul_eq_add_self 5

example (a b : ℝ) : a + (b + b) = a + 2 * b := by
  exact HighSchoolMath.Algebra.add_twice_eq a b

example (a b : ℝ) :
    (a + b) + (a + b) = 2 * a + 2 * b := by
  exact HighSchoolMath.Algebra.double_sum a b

example (a : ℝ) : (a + a) + a = 3 * a := by
  exact HighSchoolMath.Algebra.triple_eq_three_mul a


example (x y : ℝ) (h : x = y) : x + 7 = y + 7 := by
  exact HighSchoolMath.Algebra.add_same_right x y (7:ℝ) h

example (x y : ℝ) (h : x + 5 = y + 5) : x = y := by
  revert h
  exact HighSchoolMath.Algebra.cancel_add_right x y (5:ℝ)

example (x y : ℝ) (h : x = y) : 2 * x = 2 * y := by
  revert h
  exact HighSchoolMath.Algebra.double_eq_of_eq x y

example (x y : ℝ) (h : 3 * x = 3 * y) : x = y := by
  have ha : (3:ℝ) ≠ 0 := by norm_num
  revert h
  exact HighSchoolMath.Algebra.cancel_mul_left (3:ℝ) x y ha


example : ((11 : ℝ) - 4) + 4 = 11 := by
  exact HighSchoolMath.Algebra.sub_add_restore 11 4

example (x y : ℝ) (h : x + 5 = y + 5) : x = y := by
  revert h
  exact (HighSchoolMath.Algebra.add_same_right_iff x y 5).mp

example (x y : ℝ) : (0 : ℝ) * x = 0 * y := by
  apply (HighSchoolMath.Algebra.mul_same_left_iff 0 x y).mpr;
  left
  rfl

example : ∃ x : ℝ, x + 3 = 10 := by
  exact HighSchoolMath.Algebra.exists_add_solution 3 10

example :
    ∃ x : ℝ, x + 3 = 10 ∧
      ∀ y : ℝ, y + 3 = 10 → y = x := by
  exact HighSchoolMath.Algebra.exists_add_solution_unique 3 10
