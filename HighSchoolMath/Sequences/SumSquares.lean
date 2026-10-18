/-
Copyright (c) 2026 wmtai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: wmtai
-/
module

public import HighSchoolMath.Basic

/-!
Sum of suqares
-/

@[expose] public section

open scoped BigOperators

namespace HighSchoolMath.Sequences

def sumSquares (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (k : ℝ) ^ 2

@[simp] theorem sumSquares_zero :
    sumSquares 0 = 0 := by
  unfold sumSquares
  ring

theorem sumSquares_succ (n : ℕ) :
    sumSquares (n + 1) =
      sumSquares n + (n : ℝ) ^ 2 := by
  unfold sumSquares
  rw [Finset.sum_range_succ]

theorem sumSquares_nonneg (n : ℕ) :
    0 ≤ sumSquares n := by
  induction n with
  | zero =>
    rw [sumSquares_zero]
  | succ k hk =>
    rw [sumSquares_succ]
    have temp : 0 ≤ (k:ℝ)^2 := by exact sq_nonneg (k:ℝ)
    nlinarith [temp, hk]

theorem sumSquares_six (n : ℕ) :
    6 * sumSquares n =
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) := by
  induction n with
  | zero =>
    rw [sumSquares_zero]; ring
  | succ k hk =>
    rw [sumSquares_succ, mul_add, hk, Nat.cast_add, Nat.cast_one]
    ring

theorem sumSquares_formula (n : ℕ) :
    sumSquares n =
      (n : ℝ) * ((n : ℝ) - 1) *
        (2 * (n : ℝ) - 1) / 6 := by
  rw [← sumSquares_six, mul_div_assoc, mul_div_cancel₀ (sumSquares n) (by norm_num)]



end HighSchoolMath.Sequences
