module

public import HighSchoolMath.Algebra.LinearEquations

/-!
Affine functions over the real numbers.
-/

public section

namespace HighSchoolMath.Algebra

def affine (a b : ℝ) : ℝ → ℝ :=
  fun x => a * x + b

theorem affine_apply (a b x : ℝ) :
    affine a b x = a * x + b := by
  rfl

theorem affine_id :
    affine 1 0 = (fun x : ℝ => x) := by
  funext x
  simp [affine]

theorem affine_comp (a b c d : ℝ) :
    affine a b ∘ affine c d =
      affine (a * c) (a * d + b) := by
  funext x
  change a * (c * x + d) + b = (a*c) * x + (a*d+b)
  ring

theorem affine_injective (a b : ℝ) (ha : a ≠ 0) :
    Function.Injective (affine a b) := by
  intro x y h
  change a * x + b = a * y + b at h
  have t: a*x = a*y := by exact cancel_add_right (a*x) (a*y) b h
  apply cancel_mul_left a x y ha t

theorem affine_injective_iff (a b : ℝ) :
    Function.Injective (affine a b) ↔ a ≠ 0 := by
  constructor
  <;> intro h
  · by_contra hc
    unfold Function.Injective affine at h
    rw [hc] at h
    specialize h (a₁ := 0) (a₂ := 1)
    norm_num at h
  · exact affine_injective a b h

theorem affine_eq_iff (a b c d : ℝ) :
    affine a b = affine c d ↔ a = c ∧ b = d := by
  constructor
  <;> intro h
  · apply congrFun at h
    unfold affine at h
    have t1: b = d := by
      specialize h 0
      linarith
    have t2: a+b = c+d := by
      specialize h 1
      linarith
    rw [t1] at t2
    constructor
    · linarith
    · linarith
  · rcases h with ⟨h1,h2⟩; rw [h1,h2]

end HighSchoolMath.Algebra
