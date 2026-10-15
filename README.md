# HighSchoolMath

A small Lean 4 library of elementary high-school mathematics, built on mathlib.
The current library contains arithmetic checks, algebraic identities over the
real numbers, equation transformations, and existence and uniqueness results
for equations of the form `x + b = c`.

## Toolchain and dependencies

| Component | Version |
| --- | --- |
| Lean | `leanprover/lean4:v4.35.0-rc4` |
| mathlib | `v4.35.0-rc4` |

The compiler version is recorded in [lean-toolchain](lean-toolchain).
[lakefile.toml](lakefile.toml) declares the mathlib dependency, and
[lake-manifest.json](lake-manifest.json) records the resolved dependency revisions.

## Getting started

Install Lean's toolchain manager, `elan`, so that `lean` and `lake` are available.
Then clone the project and download the precompiled mathlib cache:

```bash
git clone https://github.com/wmtai/HighSchoolMath.git
cd HighSchoolMath
lake exe cache get
```

Build the public library:

```bash
lake build
```

Build the client examples to check the public interface and number-system examples:

```bash
lake build +HighSchoolMath.Examples
```

Lake stores dependencies and generated build files in `.lake/`, which is ignored
by Git.

## Using the library

Import the public root module to access the library's theorems:

```lean
import HighSchoolMath

example (x : ℝ) : x + x = 2 * x := by
  exact HighSchoolMath.Algebra.twice_eq_two_mul x

example (b c : ℝ) :
    ∃ x : ℝ, x + b = c ∧
      ∀ y : ℝ, y + b = c → y = x := by
  exact HighSchoolMath.Algebra.exists_add_solution_unique b c
```

The second example states that a solution exists and that every other solution
equals the chosen solution.

## Current modules

| Module | Contents |
| --- | --- |
| [HighSchoolMath](HighSchoolMath.lean) | Public entry point re-exporting the mathematical modules |
| [HighSchoolMath.Basic](HighSchoolMath/Basic.lean) | Arithmetic checks and natural-number successor subtraction |
| [HighSchoolMath.Algebra.Identities](HighSchoolMath/Algebra/Identities.lean) | Elementary real identities, repeated addition, and distributivity |
| [HighSchoolMath.Algebra.LinearEquations](HighSchoolMath/Algebra/LinearEquations.lean) | Equality transformations and additive and nonzero multiplicative cancellation |
| [HighSchoolMath.Algebra.EquationLogic](HighSchoolMath/Algebra/EquationLogic.lean) | Cancellation equivalences and existence and uniqueness of additive-equation solutions |
| [HighSchoolMath.Examples](HighSchoolMath/Examples.lean) | Client examples, number systems, coercions, and theorem reuse |

## GitHub workflows

The repository includes workflows for building the project and documentation,
tagging Lean toolchain updates, and manually checking dependency updates.

For documentation deployment, set **Settings → Pages → Build and deployment →
Source** to **GitHub Actions**. To allow the dependency-update workflow to open
pull requests, enable **Settings → Actions → General → Allow GitHub Actions to
create and approve pull requests**.
