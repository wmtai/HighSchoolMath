/-
Copyright (c) 2026 wmtai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: wmtai
-/
module

public import Mathlib

/-!
# Basic Arithmetic
-/

public section

namespace HighSchoolMath

theorem addition_check : (8 : ℝ) + 7 = 15 := by
  norm_num

theorem square_check : (6 : ℝ) ^ 2 = 36 := by
  norm_num

theorem successor_sub_one (n : ℕ) : (n + 1) - 1 = n := by
  rfl

end HighSchoolMath
