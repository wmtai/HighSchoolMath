/-
Copyright (c) 2026 wmtai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: wmtai
-/
module

public import HighSchoolMath.Algebra.LinearEquations

/-!
Logical statements and solution properties for elementary equations.
-/

public section

namespace HighSchoolMath.Algebra

theorem sub_add_restore (x y : ℝ) :
    (x - y) + y = x := by
  exact sub_add_cancel x y

theorem add_same_right_iff (x y c : ℝ) :
    x + c = y + c ↔ x = y := by
  constructor
  · exact cancel_add_right x y c
  · intro h; rw [h]

theorem mul_same_left_iff (a x y : ℝ) :
    a * x = a * y ↔ a = 0 ∨ x = y := by
  constructor
  <;> intro h
  · by_cases ha : a = 0
    · rw [ha]; left; rfl
    · right; push Not at ha; revert h; exact cancel_mul_left a x y ha
  · rcases h with h | h
    · simp [h]
    · simp [h]

theorem exists_add_solution (b c : ℝ) :
    ∃ x : ℝ, x + b = c := by
  refine ⟨c-b, ?_⟩
  exact sub_add_restore c b

theorem exists_add_solution_unique (b c : ℝ) :
    ∃ x : ℝ, x + b = c ∧
      ∀ y : ℝ, y + b = c → y = x := by
  refine ⟨c-b, ?_,?_⟩
  · exact sub_add_restore c b
  · intro y h; rw [← h, add_sub_assoc]; symm; exact add_sub_self_eq_left y b


end HighSchoolMath.Algebra
