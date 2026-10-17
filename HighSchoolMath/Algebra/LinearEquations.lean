module

public import HighSchoolMath.Algebra.Fractions

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


theorem linear_eq_iff (a b c x : ℝ) (ha : a ≠ 0) :
    a * x + b = c ↔ x = (c - b) / a := by
  constructor
  <;> intro h
  · rw [← h]; field_simp [ha]; ring
  · rw [h]; field_simp [ha]; ring

theorem linear_exists_unique (a b c : ℝ) (ha : a ≠ 0) :
    ∃ x : ℝ, a * x + b = c ∧
      ∀ y : ℝ, a * y + b = c → y = x := by
  refine ⟨(c - b) / a, ?_, ?_⟩
  · field_simp [ha]; ring
  · intro y h
    rw [← h]; field_simp [ha]; ring

theorem linear_zero_all_iff (b c : ℝ) :
    (∀ x : ℝ, (0 : ℝ) * x + b = c) ↔ b = c := by
  constructor
  <;> intro h
  · specialize h 1; rw [zero_mul, zero_add] at h; exact h
  · intro x; rw [zero_mul, zero_add]; exact h

theorem linear_zero_no_solution_iff (b c : ℝ) :
    (¬ ∃ x : ℝ, (0 : ℝ) * x + b = c) ↔ b ≠ c := by
  constructor
  <;> intro h
  · push Not at h; specialize h 0; rw [zero_mul, zero_add] at h; exact h
  · intro hc; obtain ⟨x,hc⟩ := hc; rw [zero_mul, zero_add] at hc; rw[hc] at h; norm_num at h

theorem linear_has_solution_iff (a b c : ℝ) :
    (∃ x : ℝ, a * x + b = c) ↔ a ≠ 0 ∨ b = c := by
  constructor
  <;> intro h
  · obtain ⟨ x,h⟩ := h
    by_cases h1 : a ≠ 0
    · left; exact h1
    · push Not at h1; rw [h1, zero_mul, zero_add] at h; right; exact h
  · rcases h with h|h
    · have t:= linear_exists_unique a b c h; obtain ⟨x,h1⟩ := t; refine ⟨x,h1.left⟩
    · refine ⟨0,?_⟩; rw [mul_zero, zero_add,h]


end HighSchoolMath.Algebra
