module

public import HighSchoolMath.Algebra.LinearEquations

/-!
Linear inequalities and their solution sets over the real numbers.
-/

public section

namespace HighSchoolMath.Algebra

def linearLeSolutions (a b c : ℝ) : Set ℝ :=
  {x : ℝ | a * x + b ≤ c}

theorem linear_le_iff_of_pos (a b c x : ℝ) (ha : 0 < a) :
    a * x + b ≤ c ↔ x ≤ (c - b) / a := by
  rw [le_div_iff₀' ha]
  constructor
  <;> intro h
  <;> linarith

theorem linear_le_iff_of_neg (a b c x : ℝ) (ha : a < 0) :
    a * x + b ≤ c ↔ (c - b) / a ≤ x := by
  rw [div_le_iff_of_neg ha]
  constructor
  <;> intro h
  <;> linarith

theorem linear_le_solutions_of_pos (a b c : ℝ) (ha : 0 < a) :
    linearLeSolutions a b c = Set.Iic ((c - b) / a) := by
  ext x
  change a * x + b ≤ c ↔ x ≤ (c - b) / a
  exact linear_le_iff_of_pos a b c x ha


theorem linear_le_solutions_of_neg (a b c : ℝ) (ha : a < 0) :
    linearLeSolutions a b c = Set.Ici ((c - b) / a) := by
  ext x
  change a * x + b ≤ c ↔ (c - b) / a ≤ x
  exact linear_le_iff_of_neg a b c x ha


theorem linear_le_solutions_zero_all (b c : ℝ) (hbc : b ≤ c) :
    linearLeSolutions 0 b c = Set.univ := by
  ext x
  simp [linearLeSolutions, hbc]

theorem linear_le_solutions_zero_none (b c : ℝ) (hcb : c < b) :
    linearLeSolutions 0 b c = ∅ := by
  have hnot: ¬ b ≤ c := by linarith
  ext x
  simp [linearLeSolutions, hnot]

end HighSchoolMath.Algebra
