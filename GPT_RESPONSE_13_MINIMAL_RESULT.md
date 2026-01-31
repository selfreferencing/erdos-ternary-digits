# GPT Response 13: Minimal New Result Analysis

**Date:** January 31, 2026
**Prompt:** PROMPT_LEVEL_C_2_MINIMAL_RESULT.txt
**Type:** Technical Analysis

---

## Executive Summary

Three archetypal "minimal sufficient theorems" identified. The most atomic is **Theorem A**: an exponential-accuracy discrepancy bound for Cantor cylinders that would directly close the log-time gap. Also clarifies that Lagarias Conjecture B (dim = 0) does NOT by itself imply Erdős.

---

## The Log-Time Obstruction (Precise Statement)

Let C₀₁ ⊂ Z₃ be the 3-adic Cantor set (digits only 0,1).

Define E := {n ≥ 0 : 2^n ∈ C₀₁ ∩ N}.

**Erdős conjecture**: E = {0, 2, 8}.

**The obstruction**: At size 3^k, Cantor set density is (2/3)^k, but number of powers 2^n below 3^k is only ~k. Any argument producing only polynomial-quality error (~1/k) can't beat exponentially tiny target ~(2/3)^k.

---

## Three Minimal Sufficient Theorems

### Theorem A: Quantitative Shrinking-Target Estimate

For each k ≥ 1, let:
- A_k := {x ∈ Z/3^k Z : base-3 digits of x (mod 3^k) lie in {0,1}}
- |A_k| = 2^k, so |A_k|/3^k = (2/3)^k
- N(k) := ⌊log₂(3^k)⌋ ~ k log₂ 3

**Theorem A (Exponential-accuracy discrepancy)**:
There exist C > 0 and δ > 0 such that for all k ≥ 1:

|#{n₀ ≤ n ≤ N(k) : 2^n mod 3^k ∈ A_k} - (N(k) - n₀ + 1) · |A_k|/3^k| ≤ C · 3^{-δk}

for some fixed cutoff n₀ (say n₀ = 20).

**Why this settles Erdős**:
- Main term is ~k · (2/3)^k < 10^{-6} for moderate k
- Error C·3^{-δk} is exponentially small
- For large k, count must be 0 (integer trapped between ±1/2)
- Combined with finite computational check → exactly {0,2,8}

**Weaker sufficient variant (upper bound only)**:
#{n₀ ≤ n ≤ N(k) : 2^n mod 3^k ∈ A_k} ≤ C · k · (2/3)^{(1+ε)k}

for some ε > 0. Since RHS drops below 1, get zero hits.

---

### Theorem B: Orbit-Cantor Rigidity

**Theorem B (Strong rigidity)**:
If λ ∈ Z₃ has infinitely many n with λ·2^n ∈ Σ_{3,2̄} (digit-2-avoiding), then λ must belong to an explicitly classifiable "algebraic/automatic" set (e.g., finite union of eventually periodic 3-adic expansions, or finite set of rationals in Q₃).

In particular, λ = 1 is not among them.

**Why this settles Erdős**: Erdős is exactly the λ = 1 case.

**Why it's hard**: Target Σ_{3,2̄} is fractal, not algebraic subvariety. Known "dynamical Mordell-Lang" theorems don't apply. Need new rigidity principle for orbits intersecting self-similar digit sets.

---

### Theorem C: Bounded Weight Bridge

**Lemma C' (Bounded weight of any solution)**:
There exists absolute B ≤ 25 such that whenever 2^n has ternary digits only {0,1}, it has at most B digits equal to 1.

**Why this settles Erdős**: Dimitrov-Howe already proved ≤25 ones ⇒ n ∈ {0,2,8}. This lemma would be the exact bridge.

**Why it's implausible**: Heuristically, a "random" 0/1 ternary string of length k has ~k/2 ones. Solutions (if any existed) would not be expected to have bounded weight. Logically minimal but not natural.

---

## Four Conditional "If X Then Erdős" Statements

### Conditional 1: Quantitative Normality

**(X1)** There exist c, C > 0 such that for every n, the probability that base-3 expansion of 2^n contains no digit 2 is ≤ C·e^{-c·#digits(2^n)}.

Then Σ_n C·e^{-c·#digits} < ∞, and Borel-Cantelli yields finiteness.

### Conditional 2: Lagarias Conjecture E (Pattern Appearance)

**(X2)** For base 3, every finite ternary digit pattern occurs in 2^n for all sufficiently large n.

Taking one-digit pattern "2" yields Erdős immediately.

### Conditional 3: Discrete Log Pseudorandomness

**(X3)** For each k, the set {n mod (2·3^{k-1}) : 2^n mod 3^k ∈ A_k} behaves like uniformly random subset of density (2/3)^k:

#{0 ≤ n ≤ N(k) : 2^n mod 3^k ∈ A_k} ≪ k · (2/3)^k

This is Theorem A in upper-bound form.

### Conditional 4: Conjecture B + Amplification Lemma

**(X4) Amplification lemma**: If λ ∈ E(Z₃), then there exists Cantor-like subset K_λ ⊂ E(Z₃) of **positive** Hausdorff dimension containing λ.

Then Conjecture B (dim = 0) would imply E(Z₃) is empty, hence 1 ∉ E(Z₃), proving Erdős.

---

## Relationship: Conjecture B vs Erdős

### What Conjecture B Says

Lagarias defines E(Z₃) = {λ ∈ Z₃ : λ·2^n ∈ Σ_{3,2̄} for infinitely many n}

**Conjecture B**: dim_H(E(Z₃)) = 0

Best bound: dim_H(E(Z₃)) ≤ log₃(φ) ≈ 0.438 (Abram-Bolshakov-Lagarias)

### Does Conjecture B Imply Erdős?

**NO.** A set can have Hausdorff dimension 0 and still contain the specific point λ = 1.

dim_H(E) = 0 does NOT logically force 1 ∉ E.

### Does Erdős Imply Conjecture B?

**NO.** Erdős only says λ = 1 is not exceptional. Conjecture B is uniform over all λ ∈ Z₃.

### How Are They Connected?

They're connected by the *hope* that exceptional behavior is "rigid" enough that presence of even one exceptional point forces richer exceptional set (positive dimension), in which case Conjecture B would indirectly exclude λ = 1.

**But that amplification/rigidity statement is not currently available.**

---

## The Pragmatic "Minimal Leap"

### Closest to Existing Tools

A new mechanism converting automaton/fractal dimension control (Lagarias + Abram-Bolshakov-Lagarias) into statement about:
- A **specific orbit point** (λ = 1), OR
- **Short-time visits** (log-time regime)

Current dimension technology controls "how big the set of bad starting points can be" but doesn't say "this specific starting point is not bad."

### Logically Smallest Bridge

Theorem A (or upper-bound form) is about as atomic as it gets: exactly the missing exponential-accuracy estimate that turns heuristic "expected hits = k(2/3)^k" into proof.

---

## Key Insight

> **Any result that gives exponentially small error at digit resolution k for the orbit {2^n} is strong enough to close the log-time gap and settle Erdős.**

The core requirement: exponential accuracy, not polynomial. This is what separates the problem from standard equidistribution.

---

## Summary Table

| Statement | Type | What It Would Prove |
|-----------|------|---------------------|
| Theorem A | Discrepancy | Exponential error → zero hits for large k |
| Theorem B | Rigidity | λ = 1 not in classifiable exceptional set |
| Lemma C' | Bridge | Weight ≤ 25 → Dimitrov-Howe finishes |
| X1 | Conditional | Exponential tails → Borel-Cantelli |
| X2 | Conditional | Pattern "2" appears → done |
| X3 | Conditional | Pseudorandomness → upper bound |
| X4 | Conditional | Amplification + dim = 0 → empty |

---

## Key References

- Lagarias: arXiv:math/0512006 (Conjectures A, B, E)
- Abram-Bolshakov-Lagarias: arXiv:1508.05967 (dim ≤ log₃φ)
- Dimitrov-Howe: arXiv:2105.06440 (≤25 ones)
- Saye: arXiv:2202.13256 (verification to 5.9×10²¹)
- Ren-Roettger: arXiv:2511.03861 (digit frequencies)
