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


example (n : ℕ) : n + n = 2 * n := by
  exact HighSchoolMath.Algebra.twice_eq_two_mul n

example (z : ℤ) : z + z = 2 * z := by
  exact HighSchoolMath.Algebra.twice_eq_two_mul z

example (q : ℚ) : q + q = 2 * q := by
  exact HighSchoolMath.Algebra.twice_eq_two_mul q

-- Exercise 2.1: reuse algebraic identities through the public interface.

example (x y z : ℝ) : (x + y) + z = (x + z) + y := by
  exact HighSchoolMath.Algebra.add_rearrange x y z

example (a b x y : ℝ) :
    a * x + a * y + b * x + b * y = (a + b) * (x + y) := by
  exact HighSchoolMath.Algebra.factor_four_terms a b x y

example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  exact HighSchoolMath.Algebra.square_add x y

example (x y : ℝ) : (x - y) ^ 2 = x ^ 2 - 2 * x * y + y ^ 2 := by
  exact HighSchoolMath.Algebra.square_sub x y

example (x y : ℝ) : x ^ 2 - y ^ 2 = (x - y) * (x + y) := by
  exact HighSchoolMath.Algebra.difference_of_squares x y


example (a b k : ℝ) (hk : k ≠ 0) :
    (a * k) / (b * k) = a / b := by
  exact HighSchoolMath.Algebra.cancel_fraction_factor a b k hk

example (a c : ℝ) :
    a / 2 + c / 3 = (a * 3 + c * 2) / (2 * 3) := by
  exact HighSchoolMath.Algebra.fraction_add
    a 2 c 3 (by norm_num) (by norm_num)

example (a c : ℝ) :
    a / 3 - c / 5 = (a * 5 - c * 3) / (3 * 5) := by
  exact HighSchoolMath.Algebra.fraction_sub
    a 3 c 5 (by norm_num) (by norm_num)

example (a c : ℝ) :
    a / 2 = c / 3 ↔ a * 3 = c * 2 := by
  exact HighSchoolMath.Algebra.fraction_eq_iff_cross_mul
    a 2 c 3 (by norm_num) (by norm_num)

example (x y : ℝ) (hsum : x + y ≠ 0) :
    (x ^ 2 - y ^ 2) / (x + y) = x - y := by
  exact HighSchoolMath.Algebra.difference_of_squares_div x y hsum


example (x : ℝ) : 2 * x + 3 = 11 ↔ x = 4 := by
  have h := HighSchoolMath.Algebra.linear_eq_iff
    2 3 11 x (by norm_num)
  norm_num at h
  exact h

example (x : ℝ) : (-2) * x + 3 = 11 ↔ x = -4 := by
  have h := HighSchoolMath.Algebra.linear_eq_iff
    (-2) 3 11 x (by norm_num)
  norm_num at h
  simpa [neg_mul] using h

example :
    ∃ x : ℝ, 3 * x + 2 = 8 ∧
      ∀ y : ℝ, 3 * y + 2 = 8 → y = x := by
  exact HighSchoolMath.Algebra.linear_exists_unique
    3 2 8 (by norm_num)

example : ∀ x : ℝ, (0 : ℝ) * x + 5 = 5 := by
  exact (HighSchoolMath.Algebra.linear_zero_all_iff 5 5).mpr rfl

example : ¬ ∃ x : ℝ, (0 : ℝ) * x + 2 = 5 := by
  apply (HighSchoolMath.Algebra.linear_zero_no_solution_iff 2 5).mpr
  norm_num

example (a : ℝ) : ∃ x : ℝ, a * x + 4 = 4 := by
  apply (HighSchoolMath.Algebra.linear_has_solution_iff a 4 4).mpr
  right
  rfl


example (x : ℝ) : 2 * x + 3 ≤ 11 ↔ x ≤ 4 := by
  have h := HighSchoolMath.Algebra.linear_le_iff_of_pos
    2 3 11 x (by norm_num)
  norm_num at h
  exact h

example (x : ℝ) : (-2) * x + 3 ≤ 11 ↔ -4 ≤ x := by
  have h := HighSchoolMath.Algebra.linear_le_iff_of_neg
    (-2) 3 11 x (by norm_num)
  norm_num at h
  simpa [neg_mul] using h

example :
    HighSchoolMath.Algebra.linearLeSolutions 2 3 11 = Set.Iic 4 := by
  have h := HighSchoolMath.Algebra.linear_le_solutions_of_pos
    2 3 11 (by norm_num)
  norm_num at h
  exact h

example :
    HighSchoolMath.Algebra.linearLeSolutions (-2) 3 11 =
      Set.Ici (-4) := by
  have h := HighSchoolMath.Algebra.linear_le_solutions_of_neg
    (-2) 3 11 (by norm_num)
  norm_num at h
  exact h

example :
    HighSchoolMath.Algebra.linearLeSolutions 0 5 5 = Set.univ := by
  exact HighSchoolMath.Algebra.linear_le_solutions_zero_all
    5 5 (by norm_num)

example :
    HighSchoolMath.Algebra.linearLeSolutions 0 7 5 = ∅ := by
  exact HighSchoolMath.Algebra.linear_le_solutions_zero_none
    7 5 (by norm_num)


open HighSchoolMath.Algebra

example (a b x : ℝ) : affine a b x = a * x + b := by
  exact affine_apply a b x

example : affine 1 0 = (fun x : ℝ => x) := by
  exact affine_id

example : affine 2 3 ∘ affine 4 5 = affine 8 13 := by
  have h := affine_comp 2 3 4 5
  norm_num at h
  exact h

example : Function.Injective (affine 3 (-7)) := by
  exact affine_injective 3 (-7) (by norm_num)

example : ¬ Function.Injective (affine 0 5) := by
  rw [affine_injective_iff]
  simp

example (a b : ℝ) :
    affine a b = affine 2 3 ↔ a = 2 ∧ b = 3 := by
  exact affine_eq_iff a b 2 3

example (x : ℝ) : affine 2 3 x = 11 ↔ x = 4 := by
  have h := linear_eq_iff 2 3 11 x (by norm_num)
  norm_num at h
  rw [← h, affine_apply]

example :
    {x : ℝ | affine (-2) 3 x ≤ 11} = Set.Ici (-4) := by
  ext x
  norm_num
  rw [affine_apply (-2) 3 x, linear_le_iff_of_neg (-2) 3 11 x (show -2 < 0 by norm_num)]
  norm_num


open HighSchoolMath.Quadratics

example (a b c x : ℝ) :
    (⟨a, b, c⟩ : Quadratic).eval x =
      a * x ^ 2 + b * x + c := by
  exact Quadratic.eval_mk a b c x

example (q : Quadratic) : q.eval 0 = q.c := by
  exact Quadratic.eval_zero q

example (x : ℝ) :
    (⟨1, -5, 6⟩ : Quadratic).eval x =
      (x - 2) * (x - 3) := by
  have h := Quadratic.eval_factored 1 2 3 x
  norm_num at h
  exact h

example (x : ℝ) :
    (⟨1, -5, 6⟩ : Quadratic).IsRoot x ↔
      x = 2 ∨ x = 3 := by
  have h := Quadratic.isRoot_factored_iff
    1 2 3 x (by norm_num)
  norm_num at h
  exact h

example (q : Quadratic) (x : ℝ) :
    (2 * q.a * x + q.b) ^ 2 - q.discrim =
      4 * q.a * q.eval x := by
  exact Quadratic.completing_square q x

example (q : Quadratic) (x : ℝ) (ha : q.a ≠ 0) :
    q.IsRoot x ↔
      (2 * q.a * x + q.b) ^ 2 = q.discrim := by
  exact Quadratic.isRoot_iff_completed_square q x ha

example : (⟨1, -5, 6⟩ : Quadratic).IsRoot 3 := by
  have h := Quadratic.rootPlus_isRoot
    (⟨1, -5, 6⟩ : Quadratic)
    (by norm_num)
    (by norm_num [Quadratic.discrim])
  norm_num [Quadratic.rootPlus, Quadratic.discrim] at h
  exact h

example : (⟨1, -5, 6⟩ : Quadratic).IsRoot 2 := by
  have h := Quadratic.rootMinus_isRoot
    (⟨1, -5, 6⟩ : Quadratic)
    (by norm_num)
    (by norm_num [Quadratic.discrim])
  norm_num [Quadratic.rootMinus, Quadratic.discrim] at h
  exact h

example (x : ℝ) :
    (⟨1, -4, 4⟩ : Quadratic).IsRoot x ↔ x = 2 := by
  have h := Quadratic.isRoot_factored_iff
    1 2 2 x (by norm_num)
  norm_num at h
  exact h

-- Positive discriminant: exactly two formula roots.
example (x : ℝ) :
    (⟨1, -5, 6⟩ : Quadratic).IsRoot x ↔
      x = 3 ∨ x = 2 := by
  have h := Quadratic.isRoot_iff_formula
    (⟨1, -5, 6⟩ : Quadratic) x (by norm_num)
    (by norm_num [Quadratic.discrim])
  norm_num [
    Quadratic.rootPlus, Quadratic.rootMinus, Quadratic.discrim
  ] at h
  exact h

example :
    (⟨1, -5, 6⟩ : Quadratic).rootPlus ≠
      (⟨1, -5, 6⟩ : Quadratic).rootMinus := by
  exact Quadratic.rootPlus_ne_rootMinus
    (⟨1, -5, 6⟩ : Quadratic) (by norm_num)
    (by norm_num [Quadratic.discrim])

-- Zero discriminant: one repeated root.
example (x : ℝ) :
    (⟨1, -4, 4⟩ : Quadratic).IsRoot x ↔ x = 2 := by
  have h := Quadratic.isRoot_iff_of_discrim_eq_zero
    (⟨1, -4, 4⟩ : Quadratic) x (by norm_num)
    (by norm_num [Quadratic.discrim])
  norm_num at h
  exact h

-- Negative discriminant: no real root.
example (x : ℝ) :
    ¬ (⟨1, 0, 1⟩ : Quadratic).IsRoot x := by
  exact Quadratic.not_isRoot_of_discrim_neg
    (⟨1, 0, 1⟩ : Quadratic) x (by norm_num)
    (by norm_num [Quadratic.discrim])

example :
    ∃ x : ℝ, (⟨1, -4, 4⟩ : Quadratic).IsRoot x := by
  apply (Quadratic.exists_root_iff
    (⟨1, -4, 4⟩ : Quadratic) (by norm_num)).mpr
  norm_num [Quadratic.discrim]

-- Completing the square and attaining the minimum.
example (x : ℝ) :
    (⟨1, -4, 7⟩ : Quadratic).eval x =
      (x - 2) ^ 2 + 3 := by
  have h := Quadratic.eval_vertex_form
    (⟨1, -4, 7⟩ : Quadratic) x (by norm_num)
  norm_num [
    Quadratic.vertex, Quadratic.vertexValue, Quadratic.discrim
  ] at h
  exact h

example :
    (⟨1, -4, 7⟩ : Quadratic).eval 2 = 3 := by
  have h := Quadratic.eval_vertex
    (⟨1, -4, 7⟩ : Quadratic) (by norm_num)
  norm_num [
    Quadratic.vertex, Quadratic.vertexValue, Quadratic.discrim
  ] at h
  exact h

example (x : ℝ) :
    3 ≤ (⟨1, -4, 7⟩ : Quadratic).eval x := by
  have h := Quadratic.vertexValue_le_eval
    (⟨1, -4, 7⟩ : Quadratic) x (by norm_num)
  norm_num [Quadratic.vertexValue, Quadratic.discrim] at h
  exact h

example (x : ℝ) :
    (⟨1, -4, 7⟩ : Quadratic).eval x = 3 ↔ x = 2 := by
  have h := Quadratic.eval_eq_vertexValue_iff
    (⟨1, -4, 7⟩ : Quadratic) x (by norm_num)
  norm_num [
    Quadratic.vertex, Quadratic.vertexValue, Quadratic.discrim
  ] at h
  exact h

example :
    ∀ x : ℝ, 0 ≤ (⟨1, -4, 7⟩ : Quadratic).eval x := by
  apply (Quadratic.nonneg_everywhere_iff
    (⟨1, -4, 7⟩ : Quadratic) (by norm_num)).mpr
  norm_num [Quadratic.discrim]

-- A zero leading coefficient reduces to Chapter 2.
example (x : ℝ) :
    (⟨0, 2, -6⟩ : Quadratic).IsRoot x ↔ x = 3 := by
  have h := HighSchoolMath.Algebra.linear_eq_iff
    2 (-6) 0 x (by norm_num)
  norm_num at h
  simpa [Quadratic.IsRoot, Quadratic.eval] using h

-- Root classification also handles a negative leading coefficient.
example (x : ℝ) :
    (⟨-1, 5, -6⟩ : Quadratic).IsRoot x ↔
      x = 2 ∨ x = 3 := by
  have h := Quadratic.isRoot_iff_formula
    (⟨-1, 5, -6⟩ : Quadratic) x (by norm_num)
    (by norm_num [Quadratic.discrim])
  norm_num [
    Quadratic.rootPlus, Quadratic.rootMinus, Quadratic.discrim
  ] at h
  exact h
