module

public import HighSchoolMath.Basic

/-!
Geometric sequences and sums of their first n terms.
-/

@[expose] public section

open scoped BigOperators

namespace HighSchoolMath.Sequences

def geometric (a r : ℝ) (n : ℕ) : ℝ :=
  a * r ^ n

def geometricSum (a r : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, geometric a r k

theorem geometric_zero (a r : ℝ) :
    geometric a r 0 = a := by
  unfold geometric
  ring

theorem geometric_succ (a r : ℝ) (n : ℕ) :
    geometric a r (n + 1) = geometric a r n * r := by
  unfold geometric
  rw [pow_succ]
  ring

theorem geometricSum_succ (a r : ℝ) (n : ℕ) :
    geometricSum a r (n + 1) =
      geometricSum a r n + geometric a r n := by
  unfold geometricSum
  rw [Finset.sum_range_succ]

theorem geometricSum_mul_sub (a r : ℝ) (n : ℕ) :
    geometricSum a r n * (r - 1) =
      a * (r ^ n - 1) := by
  induction n with
  | zero =>
    rw [geometricSum]
    ring
  | succ k hk =>
    rw [geometricSum_succ, add_mul, hk, geometric]
    ring


theorem geometricSum_formula (a r : ℝ) (n : ℕ)
    (hr : r ≠ 1) :
    geometricSum a r n =
      a * (r ^ n - 1) / (r - 1) := by
  rw [← geometricSum_mul_sub]
  field_simp [hr]

theorem geometricSum_one (a : ℝ) (n : ℕ) :
    geometricSum a 1 n = (n : ℝ) * a := by
  induction n with
  | zero =>
    rw [geometricSum]
    ring
  | succ k hk =>
    rw [geometricSum, Finset.sum_range_succ]
    rw [geometricSum] at hk
    rw [hk, geometric,Nat.cast_add,Nat.cast_one]
    ring



end HighSchoolMath.Sequences
