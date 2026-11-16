# GearProof: correctness of the PrimeAtlas v7 jump gear

Lean 4.35.0 + Mathlib v4.35.0. Author: Artur Flamandzki. License: Apache-2.0.

Paper: [`paper/jump_gear.pdf`](paper/jump_gear.pdf) (source `paper/jump_gear.tex`).

The jump gear of the [PrimeAtlas](https://github.com/Flaman55/primeAtlas) engines v7 sieves the
large numbers q of a window [F, F+W) far above 2^64 without computing F mod q for each of them
(`prime_sieve/engine_jump_gear.h`). Its mathematical core is Helfgott's improved sieve of
Eratosthenes (Math. Comp. 89 (2020), 333–350).

## Main result (`GearProof/JumpGear.lean`)

`jump_block_quick_exact` (v7.2) and `jump_block_exact` (v7.0/v7.1): every landing j < J of the
block q = Q + 30 j is visited by the C loop with the exact offset, under

    8 ≤ Q,  Q + 30 J < 2^64,  Q ≤ first < 2^62 Q,  60 J ≤ Q,  1 ≤ span ≤ 2^48,
    30 · first < 2^128   (first < 2^128 / 30 ≈ 1.134 · 10^37)

`cS_overflow`: above this bound and below the engines' earlier guard (first < 2^126), S is
computed wrongly (counterexample first = 1.2 · 10^37). The engines now use the proved bound
(primeAtlas commit `27fe0f5`). `gaps_certificate` lets a block keep the previous block's
three-gap steps; engine v7.4 uses it (commit `ab4491b`).

Models: C as functions on ℕ with explicit mod 2^64 / 2^128; double by the standard model
(every operation x(1+δ), |δ| ≤ 2^-53). Axioms: propext, Classical.choice, Quot.sound.

## Cost model (`GearProof/CostModel.lean`)

The gear threshold p* and block factor f* are the optimum of the v7.1/v7.2 cost model
(classic sieve 1/ln q, gear C/q per unit q, C = a·√(F/W) + b·W): `threshold_optimal`,
`iterP_error`, `fixedPoint_exists`, `blockCost_min`, `blockCost_clamp_min`, `model_optimal`.
The constants a, b are fitted to measurements; that the model describes the machine is not a
theorem.

## Build

    lake exe cache get
    lake build
