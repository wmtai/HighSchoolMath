/-
Copyright (c) 2026 wmtai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: wmtai
-/
module

import HighSchoolMath

/-!
# Tests
-/

open scoped BigOperators

example (a d : ℝ) : HighSchoolMath.Sequences.arithmetic a d 0 = a := by
  simp

example (a r : ℝ) : HighSchoolMath.Sequences.geometric a r 0 = a := by
  simp

example : HighSchoolMath.Sequences.sumSquares 0 = 0 := by
  simp

example (q : HighSchoolMath.Quadratics.Quadratic) : q.eval 0 = q.c := by
  simp

example (p q : HighSchoolMath.Geometry.Point) :
  HighSchoolMath.Geometry.pointDist p q = 0 ↔ p = q := by
  simp

-- The sum-of-squares interface is available through the public root import.
example (n : ℕ) :
    HighSchoolMath.Sequences.sumSquares (n + 1) =
      HighSchoolMath.Sequences.sumSquares n + (n : ℝ) ^ 2 := by
  exact HighSchoolMath.Sequences.sumSquares_succ n

example (n : ℕ) : 0 ≤ HighSchoolMath.Sequences.sumSquares n := by
  exact HighSchoolMath.Sequences.sumSquares_nonneg n

example (n : ℕ) :
    6 * HighSchoolMath.Sequences.sumSquares n =
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) := by
  exact HighSchoolMath.Sequences.sumSquares_six n

example (n : ℕ) :
    HighSchoolMath.Sequences.sumSquares n =
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
  exact HighSchoolMath.Sequences.sumSquares_formula n

-- The upper endpoint is excluded: sumSquares 1 contains only 0².
example : HighSchoolMath.Sequences.sumSquares 1 = 0 := by
  norm_num [HighSchoolMath.Sequences.sumSquares_formula]

example : HighSchoolMath.Sequences.sumSquares 10 = 285 := by
  norm_num [HighSchoolMath.Sequences.sumSquares_formula]

example : HighSchoolMath.Sequences.sumSquares 11 = 385 := by
  norm_num [HighSchoolMath.Sequences.sumSquares_formula]

-- Supplying a zero coefficient must fail to discharge the nonzero hypothesis.
/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example :
    (0 : ℝ) * 0 + 1 = 0 ↔ (0 : ℝ) = (0 - 1) / 0 :=
  HighSchoolMath.Algebra.linear_eq_iff 0 1 0 0 (by norm_num)

example (n : ℕ) :
    ∑ k ∈ Finset.range n, (2 * (k : ℝ) + 1) ^ 2 =
      (n : ℝ) * (4 * (n : ℝ) ^ 2 - 1) / 3 := by
  have h:
    ∑ k ∈ Finset.range n, (2 * (k : ℝ) + 1) ^ 2 =
      HighSchoolMath.Sequences.sumSquares (2*n) - 4 * HighSchoolMath.Sequences.sumSquares n := by
    induction n with
    | zero =>
      simp
    | succ k hk =>
      rw [Finset.sum_range_succ, hk]
      rw [show 2*(k+1) = (2*k + 1) + 1 by ring]
      rw [HighSchoolMath.Sequences.sumSquares_succ]
      rw [HighSchoolMath.Sequences.sumSquares_succ]
      rw [HighSchoolMath.Sequences.sumSquares_succ]
      push_cast
      ring
  rw [h, HighSchoolMath.Sequences.sumSquares_formula,HighSchoolMath.Sequences.sumSquares_formula]
  push_cast
  field_simp
  ring
