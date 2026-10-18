module

public import HighSchoolMath.Geometry.Coordinates
public import HighSchoolMath.Algebra.LinearEquations

/-!
Nonvertical lines and their intersections.
-/

@[expose] public section

namespace HighSchoolMath.Geometry

structure Line where
  m : ℝ
  b : ℝ

def OnLine (l : Line) (p : Point) : Prop :=
  p.2 = l.m * p.1 + l.b

noncomputable def intersectionX (l1 l2 : Line) : ℝ :=
  (l2.b - l1.b) / (l1.m - l2.m)

noncomputable def intersectionPoint (l1 l2 : Line) : Point :=
  (intersectionX l1 l2,
    l1.m * intersectionX l1 l2 + l1.b)

theorem intersection_on_both (l1 l2 : Line)
    (hm : l1.m ≠ l2.m) :
    OnLine l1 (intersectionPoint l1 l2) ∧
      OnLine l2 (intersectionPoint l1 l2) := by
  unfold OnLine intersectionPoint intersectionX
  constructor
  · field_simp [hm]
  · field_simp [hm]
    ring

theorem on_both_iff_eq_intersection
    (l1 l2 : Line) (p : Point) (hm : l1.m ≠ l2.m) :
    (OnLine l1 p ∧ OnLine l2 p) ↔
      p = intersectionPoint l1 l2 := by
  constructor
  <;> intro h
  · unfold OnLine at h
    unfold intersectionPoint intersectionX
    rcases h with ⟨h1,h2⟩
    have h3: 0 = (l2.m - l1.m) * p.1 + (l2.b - l1.b) := by linarith
    have hp1 : p.1 = (l2.b - l1.b) / (l1.m - l2.m) := by
      symm at h3
      have temp : l2.m - l1.m ≠ 0 := by
        by_contra hc;
        (have : l2.m = l1.m := by linarith [hc]);
        rw [this] at hm;
        norm_num at hm
      rw [Algebra.linear_eq_iff (l2.m - l1.m) (l2.b - l1.b) 0 p.1 temp] at h3
      rw [h3]
      field_simp [hm]
      ring
    apply Prod.ext
    · norm_num
      exact hp1
    · norm_num
      rw [hp1] at h2
      rw [h2]
      field_simp [hm]
      ring
  · rw [h]; exact intersection_on_both l1 l2 hm

theorem no_common_point_of_parallel (l1 l2 : Line)
    (hm : l1.m = l2.m) (hb : l1.b ≠ l2.b) :
    ¬ ∃ p : Point, OnLine l1 p ∧ OnLine l2 p := by
  by_contra hc
  obtain ⟨p, ⟨h1,h2⟩⟩ := hc
  unfold OnLine at *
  rw [h1, hm] at h2
  have h3: l1.b = l2.b := by linarith [h2]
  rw [h3] at hb
  norm_num at hb


theorem onLine_iff_of_same_coeffs
    (l1 l2 : Line) (p : Point)
    (hm : l1.m = l2.m) (hb : l1.b = l2.b) :
    OnLine l1 p ↔ OnLine l2 p := by
  unfold OnLine
  rw [hm,hb]

theorem has_common_point_iff (l1 l2 : Line) :
    (∃ p : Point, OnLine l1 p ∧ OnLine l2 p) ↔
      l1.m ≠ l2.m ∨ l1.b = l2.b := by
  constructor
  · contrapose
    intro h
    norm_num at h
    push Not at h
    exact no_common_point_of_parallel l1 l2 h.1 h.2
  · intro h
    rcases h with h|h
    · use (intersectionPoint l1 l2)
      exact intersection_on_both l1 l2 h
    · use (0,l1.b)
      unfold OnLine
      field_simp
      constructor
      · ring
      · rw [h]; ring


end HighSchoolMath.Geometry
