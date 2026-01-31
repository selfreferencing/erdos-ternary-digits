# Erdős Ternary Digits Conjecture - Fourier Analysis Formalization

I've been working on formalizing a Fourier-analytic approach to the **Erdős ternary digits conjecture**: every sufficiently large power of 2 contains the digit 2 in its base-3 representation.

## The Approach

The key insight is that checking whether 2^n avoids digit 2 can be modeled as a finite automaton operating on the ternary digits. For a fixed "orbit index" t, the automaton either eventually rejects (proving 2^n contains a 2) or survives forever.

The Fourier analysis shows that survival is impossible:

1. **Upper bound**: The "bias sum" Δ (measuring deviation from digit uniformity among survivors) satisfies |Δ| ≤ C' · (√3)^d via p-adic exponential sum bounds.

2. **Lower bound**: If t survives to depth d, then |Δ| ≥ 2^d (survival forces measurable bias).

3. **Contradiction**: Since √3 ≈ 1.73 < 2, eventually the upper bound beats the lower bound.

The crucial observation is that the automaton state depends only on t mod 3^14, so the Fourier transform is supported on only 3^14 frequencies (constant, independent of d). This makes the triangle inequality tractable.

## What's Formalized

**Proved by Aristotle (Harmonic):**
- `exists_depth_upper_lt_two_pow`: There exists d where C'·(√3)^d < 2^d

**Proved from axioms:**
- `fixed_t_eventually_dies`: Every orbit index t eventually fails the automaton

**Axioms used:**

| Axiom | Status |
|-------|--------|
| `padic_exp_sum_bound` | Standard result in analytic number theory (Rogers 2005, Dąbrowski-Fisher, Cochrane-Zheng) |
| `biasSum_fourier` | Bridge: Fourier support ≤ 3^14 modes (from periodicity) |
| `survives_imp_bias_lower` | Bridge: Survival forces bias ≥ 2^d |
| `biasSum_bound` | Bridge: Triangle inequality (routine) |
| `orbitBase_isUnit` | Straightforward coprimality |

## Feedback Sought

1. **Is the main axiom `padic_exp_sum_bound` stated correctly?** It asserts square-root cancellation for sums Σ_t ψ(A·g^t) where g = 4^(3^13) and ψ is a nontrivial additive character on Z/3^(15+d)Z.

2. **Does the overall structure look sound?** The bridge axioms connect the abstract Fourier machinery to concrete automaton definitions.

3. **Interest in filling the bridge axioms?** They involve Mathlib's `ZMod.dft` and automaton combinatorics.

File attached. Validated by Aristotle (Harmonic's cloud Lean 4 prover).

---

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
