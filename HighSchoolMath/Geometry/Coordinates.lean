/-
Copyright (c) 2026 wmtai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: wmtai
-/
module

public import HighSchoolMath.Basic

/-!
Coordinate points, distances, midpoints, and Pythagoras.
-/

@[expose] public section

namespace HighSchoolMath.Geometry

abbrev Point := ℝ × ℝ

def sqDist (p q : Point) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

noncomputable def pointDist (p q : Point) : ℝ :=
  Real.sqrt (sqDist p q)

noncomputable def pointMidpoint (p q : Point) : Point :=
  ((p.1 + q.1) / 2, (p.2 + q.2) / 2)

theorem sqDist_nonneg (p q : Point) :
    0 ≤ sqDist p q := by
  unfold sqDist
  nlinarith

theorem sqDist_symm (p q : Point) :
    sqDist p q = sqDist q p := by
  unfold sqDist
  ring


theorem sqDist_eq_zero_iff (p q : Point) :
    sqDist p q = 0 ↔ p = q := by
  constructor
  <;> intro h
  · unfold sqDist at h
    apply Prod.ext
    · nlinarith
    · nlinarith
  · rw [h]; unfold sqDist; ring

theorem pointDist_nonneg (p q : Point) :
    0 ≤ pointDist p q := by
  unfold pointDist
  exact Real.sqrt_nonneg (sqDist p q)

theorem pointDist_sq (p q : Point) :
    (pointDist p q) ^ 2 = sqDist p q := by
  unfold pointDist
  exact Real.sq_sqrt (sqDist_nonneg p q)

theorem pointDist_symm (p q : Point) :
    pointDist p q = pointDist q p := by
  unfold pointDist
  rw [sqDist_symm]

@[simp] theorem pointDist_eq_zero_iff (p q : Point) :
    pointDist p q = 0 ↔ p = q := by
  unfold pointDist
  rw [Real.sqrt_eq_zero (sqDist_nonneg p q)]
  exact sqDist_eq_zero_iff p q

theorem pointMidpoint_equidistant (p q : Point) :
    pointDist p (pointMidpoint p q) =
      pointDist (pointMidpoint p q) q := by
  unfold pointDist
  apply congrArg Real.sqrt
  unfold sqDist pointMidpoint
  ring

theorem pythagorean_axis_aligned (p q : Point) :
    (pointDist p q) ^ 2 =
      (pointDist p (q.1, p.2)) ^ 2 +
      (pointDist (q.1, p.2) q) ^ 2 := by
  unfold pointDist
  rw [Real.sq_sqrt (by exact sqDist_nonneg p q)]
  rw [Real.sq_sqrt (by exact sqDist_nonneg p (q.1, p.2))]
  rw [Real.sq_sqrt (by exact sqDist_nonneg (q.1, p.2) q)]
  unfold sqDist
  ring

end HighSchoolMath.Geometry
