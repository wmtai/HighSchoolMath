/-
Copyright (c) 2026 wmtai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: wmtai
-/
module

public import HighSchoolMath.Quadratics.Basic

/-!
Vertex formulas and global quadratic bounds.
-/

@[expose] public section

namespace HighSchoolMath.Quadratics.Quadratic

noncomputable def vertex (q : Quadratic) : ℝ :=
  -q.b / (2 * q.a)

noncomputable def vertexValue (q : Quadratic) : ℝ :=
  -q.discrim / (4 * q.a)

theorem eval_vertex_form (q : Quadratic) (x : ℝ)
    (ha : q.a ≠ 0) :
    q.eval x =
      q.a * (x - q.vertex) ^ 2 + q.vertexValue := by
  unfold eval vertex vertexValue discrim
  field_simp [ha]
  ring


theorem eval_vertex (q : Quadratic) (ha : q.a ≠ 0) :
    q.eval q.vertex = q.vertexValue := by
  rw [eval_vertex_form q q.vertex ha]
  ring

theorem vertexValue_le_eval (q : Quadratic) (x : ℝ)
    (ha : 0 < q.a) :
    q.vertexValue ≤ q.eval x := by
  have h := completing_square q x
  have h1 :((2 * q.a * x + q.b) ^ 2 - q.discrim) / (4 * q.a) = q.eval x := by
    rw [h]
    field_simp [ha]
  rw [← h1]
  unfold vertexValue
  field_simp
  nlinarith

theorem eval_eq_vertexValue_iff (q : Quadratic) (x : ℝ)
    (ha : q.a ≠ 0) :
    q.eval x = q.vertexValue ↔ x = q.vertex := by
  constructor
  <;> intro h
  · rw [eval_vertex_form q x ha] at h
    have h1: q.a * (x - q.vertex) ^ 2 = 0:= by linarith
    rw [mul_eq_zero] at h1
    rcases h1 with h1|h1
    · rw [h1] at ha; norm_num at ha
    · nlinarith
  · rw [h]; exact eval_vertex q ha

theorem nonneg_everywhere_iff (q : Quadratic)
    (ha : 0 < q.a) :
    (∀ x : ℝ, 0 ≤ q.eval x) ↔ q.discrim ≤ 0 := by
  constructor
  <;> intro h
  · specialize h q.vertex
    rw [eval_vertex q (show q.a ≠ 0 by nlinarith [ha]), vertexValue] at h
    field_simp [ha] at h
    nlinarith
  · intro x
    rw [eval_vertex_form q x (show q.a ≠ 0 by nlinarith [ha])]
    have h1: 0 ≤ q.vertexValue := by
      rw [vertexValue]
      field_simp [ha]
      nlinarith
    nlinarith

end HighSchoolMath.Quadratics.Quadratic
