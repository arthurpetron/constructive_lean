# ConstructiveReals

A Bishop-style constructive real analysis library for Lean 4, built against
**Lean core only** — no Mathlib, no Batteries, no dependencies of any kind.
A companion library, **ConstructiveGroups**, develops witness-carrying
constructive group theory on the same base.

Every existence claim carries a witness, every limit carries an explicit,
`Type`-level Cauchy modulus, and every load-bearing theorem is gated by
`#print axioms` to `propext` / `Quot.sound` only.  No `Classical.choice`, no
`Classical.em`, no `native_decide`, no `sorry`.

## What is in the library

The development is bottom-up:

**Rationals from scratch.**  `Rationals.lean` builds `Q'`, an unnormalized
num/den rational with decidable semantic equality and order, atop `Int` and
`Nat`.  Lean core's built-in `Rat` is not used because even
`(3 : Rat) / 4 = (3 : Rat) / 4` proved by `rfl` reports a `Classical.choice`
dependency through `Rat.decEq`.  `RationalsMul.lean`, `AbsQ.lean`,
`AbsQExtra.lean`, and `QPoly.lean` develop the ring, order, and
absolute-value algebra.

**Two constructive reals.**  `Reals.lean` defines `CReal`, a Bishop regular
Cauchy sequence in `Q'` with a `Prop`-level modulus and the one-slack order.
`RegularCReal.lean` (with `RegularCRealArith.lean`) defines `RegularCReal`,
whose canonical modulus is carried as structure *data* — making the
development choice-free and, unlike the one-slack order, **transitive**.

**Completion.**  The `CRealComplete*` family builds limits of CReal
sequences with explicit rates (`completeLimit` and its Cauchy/index/rate
variants), the backbone for extending functions from rational to real
arguments.

**Special functions, each with explicit moduli:**

- `Sqrt.lean` — square roots of positive rationals via the Heron iteration,
  with a division-free error analysis and a proved `(√a)² ≃ a`.
  `SqrtSubadd.lean`, `CRealSqrtCReal.lean` extend the algebra and lift to
  CReal arguments.
- `CubeRoot.lean` — cube roots via monotone located bisection, with
  `(∛R)³ ≃ R` and the order corollaries.
- `ExpNeg.lean`, `ExpAdd.lean`, `CRealExp.lean` and companions — the
  decaying exponential `e^{−x}` as an alternating series with geometric
  majorant, its addition law `e^{−a}·e^{−b} ≈ e^{−(a+b)}`, the contraction
  bound, and the extension to CReal exponents via the completion backbone.
- `CRealLog.lean` — the natural logarithm via the artanh series with a
  computable binary-exponent range reduction and a two-sided value sandwich.
- `Trig.lean`, `TrigAdd.lean`, `SinAddNonneg.lean`, `TrigSignedAdd*.lean`,
  `PythFull.lean`, `CRealTrig.lean`, `CRealTrigFull.lean` — sine and cosine
  as series, the addition laws, the Pythagorean identity
  `cos² + sin² ≃ 1`, and the double-angle range extension to arbitrary
  bounded nonnegative CReal angles.
- `Pi.lean` — π via the Machin formula
  `π = 16·arctan(1/5) − 4·arctan(1/239)`, with proved bounds `3 ≤ π ≤ 4`,
  positivity witnesses, and the reciprocal law for `2/π`.

Supporting series machinery: geometric tails (`Geometric.lean`,
`GeometricTail.lean`, `HalfPow.lean`), Cauchy-product corner bounds
(`CornerBound*.lean`, `CauchyConv.lean`), finite-sum algebra
(`FinSumAlg.lean`, `FinSumGeom.lean`), and budget-closure lemmas for
partial sums (`RationalTail.lean`).

**A reflective ring normaliser.**  `RingNormaliser.lean` is a *sound*
kernel-decided decision procedure for multivariate polynomial identities
over `Q'`: a reflective `PolyExpr` syntax, a canonical `NormalPoly` form,
and a soundness theorem proved from the `Q'` ring axioms alone.  Identities
beyond `omega` (nonlinear) and `ac_rfl` (needs distribution) are discharged
by `decide` on `normalize LHS = normalize RHS` — demonstrated on the
degree-2/3/4 Chu–Vandermonde convolution identities.

## The ConstructiveGroups library

A second library target, `ConstructiveGroups`, builds constructive group
theory in the same discipline (representative-producing claims return
`PSigma` data, never `Exists`; no quotient types, no `Nonempty`, no
`noncomputable`):

- `ConstructiveGroup.lean` — setoid-carried groups, homomorphisms
  respecting source/target setoids, finite enumerations with constructive
  coverage, injectively included finite central subgroups, and
  central-quotient *presentations* with explicit kernel witnesses.
- `ConstructiveRepresentationDescent.lean` — descent of homomorphisms
  through explicit central quotients, with witness-bearing faithfulness.
- `LocatedCentralQuotient.lean` — the coset-setoid construction from a
  finite central subgroup plus an explicit locator (decidability is input,
  not assumed).
- `QuaternionSign.lean`, `RationalQuaternionAlgebra.lean`,
  `RationalQuaternionQ8Fixture.lean`, `RationalQuaternionUnitNormGroup.lean`
  — the rational quaternion algebra over `Q'`: Hamilton multiplication,
  conjugation, norm; the Q8 fixture as a worked finite example; and the
  unit-norm carrier with its algebraic laws discharged by the reflective
  ring normaliser.

## Constructivity policy

The docstrings refer to three standing rules:

1. **Axiom policy.**  Every load-bearing declaration is checked with
   `#print axioms`; the permitted output is `propext` and `Quot.sound`
   only (the latter entering through Lean core's `Nat`/`Int` lemmas).
   `Classical.choice`, `Classical.em`, `native_decide`, and `sorryAx` are
   forbidden.  The `#print axioms` gates sit at the bottom of each file.

2. **No classical reals.**  Mathlib's `ℝ` (completed with
   `Classical.choice`) is never used; the library's own `CReal` /
   `RegularCReal` carry all real-number content.

3. **Moduli as data.**  Cauchy moduli and rate functions are carried at
   `Type` level (structure fields or explicit function arguments), never
   hidden inside a proof-irrelevant `Prop`-`∃` where they would need
   choice to recover.  Where a legacy `Prop`-level modulus field exists
   (`CReal.cauchy`), new constructions build the modulus as data first and
   apply it to fill the field.

## Building

```
lake build
```

The `lean-toolchain` pins `leanprover/lean4:v4.29.1`.  There are no
dependencies to fetch.  Note the library is elaboration-heavy (exact
rational arithmetic in the kernel); the lakefile caps per-process memory
at 20 GB and raises the C++ stack so failures are deterministic rather
than host-threatening.

## Provenance

This library was extracted from the constructive-analysis substrate of a
larger formalization effort.  Some docstrings retain motivating language
from that context ("budget", "per-step cost", σ̂-style trajectory framing);
the mathematics is fully general.  Issues and PRs that tighten prose,
generalize statements, or extend the API are welcome.

## License

Apache 2.0 — see `LICENSE`.
