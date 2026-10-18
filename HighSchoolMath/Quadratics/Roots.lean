/-
Copyright (c) 2026 wmtai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: wmtai
-/
module

public import HighSchoolMath.Quadratics.Basic

/-!
Verification of quadratic-formula candidates.
-/

@[expose] public section

namespace HighSchoolMath.Quadratics.Quadratic

noncomputable def rootPlus (q : Quadratic) : ℝ :=
  (-q.b + Real.sqrt q.discrim) / (2 * q.a)

noncomputable def rootMinus (q : Quadratic) : ℝ :=
  (-q.b - Real.sqrt q.discrim) / (2 * q.a)

theorem rootPlus_isRoot (q : Quadratic) (ha : q.a ≠ 0)
    (hΔ : 0 ≤ q.discrim) :
    q.IsRoot q.rootPlus := by
  rw [isRoot_iff_completed_square q (q.rootPlus) ha]
  have hlin :
    2 * q.a * q.rootPlus + q.b = Real.sqrt q.discrim := by
    unfold rootPlus
    rw [mul_comm, div_mul_cancel₀ (-q.b + √q.discrim) (show 2*q.a ≠ 0 by simp [ha])]
    ring
  rw [hlin, Real.sq_sqrt]
  exact hΔ


theorem rootMinus_isRoot (q : Quadratic) (ha : q.a ≠ 0)
    (hΔ : 0 ≤ q.discrim) :
    q.IsRoot q.rootMinus := by
  rw [isRoot_iff_completed_square q (q.rootMinus) ha]
  have hlin :
    2 * q.a * q.rootMinus + q.b = - Real.sqrt q.discrim := by
    unfold rootMinus
    rw [mul_comm, div_mul_cancel₀ (-q.b - √q.discrim) (show 2*q.a ≠ 0 by simp [ha])]
    ring
  rw [hlin, neg_sq, Real.sq_sqrt]
  exact hΔ


theorem eq_or_eq_neg_of_sq_eq (u v : ℝ) (h : u ^ 2 = v ^ 2) :
    u = v ∨ u = -v := by
  have hp : (u - v) * (u + v) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hp with hminus | hplus
  · left
    linarith
  · right
    linarith

theorem isRoot_iff_formula (q : Quadratic) (x : ℝ)
    (ha : q.a ≠ 0) (hΔ : 0 ≤ q.discrim) :
    q.IsRoot x ↔ x = q.rootPlus ∨ x = q.rootMinus := by
  constructor
  <;> intro h
  · rw [isRoot_iff_completed_square q x ha] at h
    rw [← Real.sq_sqrt hΔ] at h
    have h1: 2 * q.a * x + q.b = √q.discrim ∨ 2 * q.a * x + q.b = - √q.discrim := by
      exact eq_or_eq_neg_of_sq_eq (2 * q.a * x + q.b) (√q.discrim) h
    rcases h1 with h1|h1
    · left; rw [rootPlus, ← h1]; norm_num [ha]
    · right;
      rw [rootMinus, ← (show - (2 * q.a * x + q.b) = √q.discrim by linarith [h1])];
      norm_num [ha]
  · rcases h with h|h
    · rw [h]; exact rootPlus_isRoot q ha hΔ
    · rw [h]; exact rootMinus_isRoot q ha hΔ

theorem rootPlus_ne_rootMinus (q : Quadratic)
    (ha : q.a ≠ 0) (hΔ : 0 < q.discrim) :
    q.rootPlus ≠ q.rootMinus := by
  rw [rootPlus, rootMinus]
  by_contra hc
  rw [div_left_inj' (show 2*q.a ≠ 0 by norm_num [ha])] at hc
  have h: √q.discrim = - √q.discrim := by linarith
  have h: √q.discrim = 0 := by linarith
  have h: q.discrim = 0 := by
    rw [← Real.sq_sqrt (show 0 ≤ q.discrim by linarith [ha])];
    rw [h];
    ring
  rw [h] at hΔ
  norm_num at hΔ

theorem isRoot_iff_of_discrim_eq_zero
    (q : Quadratic) (x : ℝ)
    (ha : q.a ≠ 0) (hΔ : q.discrim = 0) :
    q.IsRoot x ↔ x = -q.b / (2 * q.a) := by
  rw [isRoot_iff_formula q x ha (show 0≤ q.discrim by linarith [hΔ])]
  rw [rootPlus, rootMinus,hΔ]
  norm_num

theorem not_isRoot_of_discrim_neg
    (q : Quadratic) (x : ℝ)
    (ha : q.a ≠ 0) (hΔ : q.discrim < 0) :
    ¬ q.IsRoot x := by
  by_contra hc
  rw [isRoot_iff_completed_square q x ha] at hc
  have h : 0≤ (2 * q.a * x + q.b) ^ 2 := by exact sq_nonneg (2 * q.a * x + q.b)
  rw [hc] at h
  nlinarith [h, hΔ]

theorem exists_root_iff (q : Quadratic) (ha : q.a ≠ 0) :
    (∃ x : ℝ, q.IsRoot x) ↔ 0 ≤ q.discrim := by
  constructor
  <;> intro h
  · obtain ⟨x,h⟩ := h
    revert h
    contrapose
    norm_num
    exact not_isRoot_of_discrim_neg q x ha
  · use q.rootPlus
    exact rootPlus_isRoot q ha h


end HighSchoolMath.Quadratics.Quadratic
