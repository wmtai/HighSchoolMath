/-
Copyright (c) 2026 wmtai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: wmtai
-/
module

public import HighSchoolMath.Basic

/-!
Quadratic coefficients, evaluation, and algebraic identities.
-/

@[expose] public section

namespace HighSchoolMath.Quadratics

structure Quadratic where
  a : ℝ
  b : ℝ
  c : ℝ

namespace Quadratic

def eval (q : Quadratic) (x : ℝ) : ℝ :=
  q.a * x ^ 2 + q.b * x + q.c

def IsRoot (q : Quadratic) (x : ℝ) : Prop :=
  q.eval x = 0

def discrim (q : Quadratic) : ℝ :=
  q.b ^ 2 - 4 * q.a * q.c

theorem eval_mk (a b c x : ℝ) :
    (⟨a, b, c⟩ : Quadratic).eval x =
      a * x ^ 2 + b * x + c := by
  unfold eval
  rfl

@[simp] theorem eval_zero (q : Quadratic) :
    q.eval 0 = q.c := by
  unfold eval
  norm_num

theorem eval_factored (a r s x : ℝ) :
    (⟨a, -a * (r + s), a * r * s⟩ : Quadratic).eval x =
      a * (x - r) * (x - s) := by
  unfold eval
  ring

theorem isRoot_factored_iff (a r s x : ℝ) (ha : a ≠ 0) :
    (⟨a, -a * (r + s), a * r * s⟩ : Quadratic).IsRoot x ↔
      x = r ∨ x = s := by
  unfold IsRoot
  rw [eval_factored,mul_eq_zero, mul_eq_zero]
  rw [sub_eq_zero, sub_eq_zero]
  constructor
  <;> intro h
  · rcases h with h|h
    · rcases h with h|h
      · rw [h] at ha; norm_num at ha
      · left; exact h
    · right; exact h
  · rcases h with h|h
    · left; right; exact h
    · right; exact h

theorem completing_square (q : Quadratic) (x : ℝ) :
    (2 * q.a * x + q.b) ^ 2 - q.discrim =
      4 * q.a * q.eval x := by
  unfold discrim eval
  ring

theorem isRoot_iff_completed_square
    (q : Quadratic) (x : ℝ) (ha : q.a ≠ 0) :
    q.IsRoot x ↔
      (2 * q.a * x + q.b) ^ 2 = q.discrim := by
  have h:= completing_square q x
  unfold IsRoot
  constructor
  <;> intro h1
  · rw [h1,mul_zero] at h; linarith
  · rw [h1, sub_self] at h; symm at h; rw [mul_eq_zero, mul_eq_zero] at h
    norm_num at h
    rcases h with h|h
    · rw [h] at ha; norm_num at ha
    · exact h


end Quadratic
end HighSchoolMath.Quadratics
