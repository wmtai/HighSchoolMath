# HighSchoolMath

A small Lean 4 library of elementary high-school mathematics, built on mathlib.
It covers algebraic identities, linear equations and inequalities, affine
functions, quadratic roots and bounds, arithmetic and geometric sequences,
sums of squares, and coordinate geometry over the real numbers.

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
lake update
lake exe cache get
```

Build the public library and regression tests:

```bash
lake build
```

Run the full verification command used by CI, including the client examples,
with warnings treated as failures:

```bash
lake build --wfail HighSchoolMath +HighSchoolMath.Examples HighSchoolMathTests
```

Lake stores dependencies and generated build files in `.lake/`, which is ignored
by Git.

## Using the library

To use the library from another Lake project, use the same Lean toolchain and
add this dependency to that project's `lakefile.toml`:

```toml
[[require]]
name = "HighSchoolMath"
git = "https://github.com/wmtai/HighSchoolMath.git"
rev = "FULL_COMMIT_SHA"
```

Replace `FULL_COMMIT_SHA` with the full hash of a published commit. Run
`lake update`, `lake exe cache get`, and `lake build` in the consuming project.
Using a commit hash keeps the dependency fixed to the chosen revision.

Import the public root module to access the library's theorems:

```lean
module

import HighSchoolMath

example (x : ℝ) : x + x = 2 * x := by
  exact HighSchoolMath.Algebra.twice_eq_two_mul x

example (b c : ℝ) :
    ∃ x : ℝ, x + b = c ∧
      ∀ y : ℝ, y + b = c → y = x := by
  exact HighSchoolMath.Algebra.exists_add_solution_unique b c

example (n : ℕ) :
    HighSchoolMath.Sequences.sumSquares n =
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
  exact HighSchoolMath.Sequences.sumSquares_formula n

example (p q : HighSchoolMath.Geometry.Point) :
    HighSchoolMath.Geometry.pointDist p q =
      HighSchoolMath.Geometry.pointDist q p := by
  exact HighSchoolMath.Geometry.pointDist_symm p q
```

The second example states that a solution exists and that every other solution
equals the chosen solution.

## Mathematical conventions

- Sequence indices start at `0`. The finite sums include indices `0` through
  `n - 1`, and a sum with `n = 0` is empty. In particular, `sumSquares n` is
  `0² + 1² + … + (n - 1)²`, so `sumSquares 10 = 285`.
- The sum formulas cast `n` to `ℝ` before subtraction. Thus `(n : ℝ) - 1`
  uses real subtraction, including when `n = 0`.
- Solving `a * x + b = c` by division requires `a ≠ 0`; separate theorems
  describe the case `a = 0`. Linear inequalities distinguish positive,
  negative, and zero coefficients. The geometric-sum division formula requires
  a ratio different from `1`, with a separate theorem for ratio `1`.
- A `Quadratic` stores coefficients `a`, `b`, and `c`, and evaluates
  `a * x² + b * x + c`. Root classification and vertex formulas require
  `a ≠ 0`. Real quadratic-formula candidates are roots when the discriminant
  is nonnegative; global lower-bound theorems assume `a > 0`.
- A `Point` is a pair of real coordinates. A `Line` represents `y = m * x + b`,
  so vertical lines are outside this representation. Intersection and
  uniqueness theorems require different slopes; other theorems handle parallel
  distinct and coincident lines.

## Current modules

| Module | Contents |
| --- | --- |
| [HighSchoolMath](HighSchoolMath.lean) | Public entry point re-exporting the mathematical modules |
| [HighSchoolMath.Basic](HighSchoolMath/Basic.lean) | Arithmetic checks and natural-number successor subtraction |
| [HighSchoolMath.Algebra.Identities](HighSchoolMath/Algebra/Identities.lean) | Elementary real identities, repeated addition, and distributivity |
| [HighSchoolMath.Algebra.LinearEquations](HighSchoolMath/Algebra/LinearEquations.lean) | Equality transformations and additive and nonzero multiplicative cancellation |
| [HighSchoolMath.Algebra.EquationLogic](HighSchoolMath/Algebra/EquationLogic.lean) | Cancellation equivalences and existence and uniqueness of additive-equation solutions |
| [HighSchoolMath.Algebra.Fractions](HighSchoolMath/Algebra/Fractions.lean) | Fraction cancellation, addition, subtraction, and cross multiplication |
| [HighSchoolMath.Algebra.Inequalities](HighSchoolMath/Algebra/Inequalities.lean) | Linear inequalities and their solution sets |
| [HighSchoolMath.Algebra.Functions](HighSchoolMath/Algebra/Functions.lean) | Affine functions, composition, injectivity, and equality |
| [HighSchoolMath.Quadratics.Basic](HighSchoolMath/Quadratics/Basic.lean) | Quadratic evaluation, discriminants, factorization, and completing the square |
| [HighSchoolMath.Quadratics.Roots](HighSchoolMath/Quadratics/Roots.lean) | Quadratic-formula candidates and exhaustive real-root classification |
| [HighSchoolMath.Quadratics.Bounds](HighSchoolMath/Quadratics/Bounds.lean) | Vertex formulas, extrema, and global nonnegativity |
| [HighSchoolMath.Sequences.Arithmetic](HighSchoolMath/Sequences/Arithmetic.lean) | Arithmetic sequences and finite sums |
| [HighSchoolMath.Sequences.Geometric](HighSchoolMath/Sequences/Geometric.lean) | Geometric sequences and finite sums, including ratio `1` |
| [HighSchoolMath.Sequences.SumSquares](HighSchoolMath/Sequences/SumSquares.lean) | Nonnegativity, recurrence, and closed formulas for sums of squares |
| [HighSchoolMath.Geometry.Coordinates](HighSchoolMath/Geometry/Coordinates.lean) | Squared distance, Euclidean distance, midpoints, and an axis-aligned Pythagorean identity |
| [HighSchoolMath.Geometry.Lines](HighSchoolMath/Geometry/Lines.lean) | Nonvertical line intersections, uniqueness, and parallel and coincident cases |
| [HighSchoolMath.Examples](HighSchoolMath/Examples.lean) | Client examples, number systems, coercions, and theorem reuse |
| [HighSchoolMathTests](HighSchoolMathTests.lean) | Public-interface checks, simp rules, numeric regressions, expected failure, and an odd-square sum identity |

## GitHub workflows

On pushes and pull requests, Lean Action CI runs the full verification command
above and an axiom audit of `HighSchoolMath`. After the build passes, pushes to
`main` and manual workflow runs on `main` also build and deploy documentation.
The repository also includes workflows for tagging Lean toolchain updates and
manually checking dependency updates.

For documentation deployment, set **Settings → Pages → Build and deployment →
Source** to **GitHub Actions**. To allow the dependency-update workflow to open
pull requests, enable **Settings → Actions → General → Allow GitHub Actions to
create and approve pull requests**.

## License

Released under the [Apache License 2.0](LICENSE).
