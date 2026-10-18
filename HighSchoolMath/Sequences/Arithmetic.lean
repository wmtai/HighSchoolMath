module

public import HighSchoolMath.Basic

/-!
Arithmetic sequences and sums of their first n terms.
-/

@[expose] public section

open scoped BigOperators

namespace HighSchoolMath.Sequences

def arithmetic (a d : ℝ) (n : ℕ) : ℝ :=
  a + (n : ℝ) * d

def arithmeticSum (a d : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, arithmetic a d k

theorem arithmetic_zero (a d : ℝ) :
    arithmetic a d 0 = a := by
  unfold arithmetic
  norm_num

theorem arithmetic_succ (a d : ℝ) (n : ℕ) :
    arithmetic a d (n + 1) = arithmetic a d n + d := by
  unfold arithmetic
  rw [Nat.cast_add, Nat.cast_one]
  ring


theorem arithmeticSum_succ (a d : ℝ) (n : ℕ) :
    arithmeticSum a d (n + 1) =
      arithmeticSum a d n + arithmetic a d n := by
  unfold arithmeticSum
  rw [Finset.sum_range_succ]

theorem arithmeticSum_twice (a d : ℝ) (n : ℕ) :
    2 * arithmeticSum a d n =
      (n : ℝ) * (2 * a + ((n : ℝ) - 1) * d) := by
  induction n with
  | zero =>
    unfold arithmeticSum
    ring
  | succ k hk =>
    rw [arithmeticSum_succ a d k, mul_add, hk, arithmetic]
    rw [Nat.cast_add, Nat.cast_one]
    ring


theorem arithmeticSum_formula (a d : ℝ) (n : ℕ) :
    arithmeticSum a d n =
      (n : ℝ) * (2 * a + ((n : ℝ) - 1) * d) / 2 := by
  have h:= arithmeticSum_twice a d n
  rw [← h, mul_div_assoc, mul_div_cancel₀ (arithmeticSum a d n) (by norm_num)]



end HighSchoolMath.Sequences
