# GPT Response 9: Comparative Analysis - Solved vs Unsolved

**Date:** January 30, 2026
**Prompt:** PROMPT_LEVEL_A_2_COMPARATIVE.txt
**Type:** Comparative Analysis

---

## Executive Summary

This response compares solved digit problems to the unsolved Erdős conjecture, identifying three "tractability templates" and four explicit barriers. **Key finding**: Erdős fails all three templates because the digit count n is unbounded, Cobham blocks automata approaches, and there's no functional equation structure.

---

## 1. The Erdős Conjecture in Diophantine Form

2^x has only digits {0,1} in base 3 iff:
$$2^x = 3^{a_1} + \cdots + 3^{a_n}, \quad 0 \leq a_1 < \cdots < a_n$$

where n = number of 1's in ternary expansion.

**Verified**: Only n ∈ {0, 2, 8} up to n ≤ 2·3^45 ≈ 5.9×10²¹ (Saye 2022)

**Status (Jan 2026)**: Still open (confirmed in arXiv:2601.12753)

---

## 2. Solved "Nearby" Problems

### A. Dimitrov-Howe (2021) - Bounded Digit Sparsity

**Solved problem**: If 2^x has no digit 2 AND at most 25 ones, then x ∈ {0, 2, 8}.

**Finiteness mechanism**: Bounded digit sparsity
- "No digit 2" + "≤25 ones" = fixed-term exponential Diophantine equation
- Fixed n makes the search space controllable

**Proof approach** (NOT Baker/LLL, but modular lifting):
1. Enumerate solutions mod small M₁ by brute force
2. "Lift" candidates from M_i to M_{i+1}, prune failures
3. Use "determinate vs indeterminate" power structure
4. For large primes, use discrete logarithms instead of enumeration

**Why it works**: Fixed n means aggressive pruning of the lifting tree.

**Contrast with Stewart**: Stewart's effective bound for n ≤ 25 is > 5.4×10⁵⁴. Dimitrov-Howe get the true bound x ≤ 8 by clever modular elimination.

**Could it extend?** In principle yes (to larger n), but combinatorial explosion - number of sums mod M balloons with n.

**Why it doesn't solve Erdős**: In Erdős, n is UNBOUNDED.

---

### B. S-unit / Stewart Methods

**What they solve**: Fixed-term exponential Diophantine equations
- For each fixed b, only finitely many m with 3^m having exactly b ones in binary

**Why they don't solve Erdős**:
- Erdős is NOT fixed sparsity - it's digit avoidance
- The number of terms n can grow with x
- S-unit gives finiteness for each fixed n, but Erdős is the UNION over all n
- No known argument forces a uniform bound on n

**Negative lesson**: Even with fixed n, Baker-effective bounds (> 5.4×10⁵⁴) are "computationally useless."

---

### C. Mahler-Type Methods

**What they solve**: Sequences with functional equations / automatic structure
- Cobham-Mahler theory: k-Mahler AND ℓ-Mahler ⇒ rational (under multiplicative independence)

**Why they don't solve Erdős**:
- The ternary digit string of 2^n has no known functional equation
- Erdős is about rare-event avoidance in a conjecturally pseudorandom sequence
- Mahler tools need explicit self-similarity

---

### D. Cobham's Theorem

**The theorem**: If k, ℓ multiplicatively independent and a sequence is both k-automatic and ℓ-automatic, then it's eventually periodic.

**Why it doesn't solve Erdős**:
- Set of integers with only digits {0,1} in base 3 is 3-automatic
- Set {2^n} is 2-automatic
- Cobham says nothing about INTERSECTION of k-automatic with ℓ-automatic sets

**Cobham actually BLOCKS a naive approach**:
- {2^n} is 2-automatic, not eventually periodic
- Therefore {2^n} CANNOT be 3-automatic
- So "show it's automatic in base 3" is not viable

---

## 3. Three Tractability Templates

### Template 1: Fixed-Dimensional Exponential Diophantine

- Digit constraint ⇒ sum of at most n base powers
- Fixed n ⇒ S-unit / Subspace theorem / Baker gives finiteness
- Clever congruences (Dimitrov-Howe) give full classification

**Missing for Erdős**: n is unbounded, no uniform dimension to grab.

### Template 2: Strong Combinatorial Structure (Automaticity)

- Automatic in two independent bases ⇒ Cobham forces periodicity

**Missing for Erdős**: Cobham implies {2^n} can't have base-3 automatic structure.

### Template 3: Self-Similarity / Functional Equations

- Mahler functions can be analyzed very effectively

**Missing for Erdős**: 2^n in base 3 has no known functional equation.

---

## 4. Four Explicit Barriers / Negative Results

### Barrier 1: Cobham Blocks Naive Automata

{2^n} is 2-automatic and not eventually periodic ⇒ cannot be 3-automatic.

### Barrier 2: S-unit Cannot Uniformize Over Unbounded Sparsity

Even at n ≤ 25, Stewart's bound is > 5.4×10⁵⁴ vs true max 8.
General Diophantine bounds are too coarse AND don't address unbounded n.

### Barrier 3: Real vs 3-adic "Two-Sided Control" Doesn't Combine

Lagarias explicitly notes:
- Can control leading digits (real model)
- Can control trailing digits (3-adic model)
- "No one knows how to combine them"
- The "middle digits" behavior is unknown

### Barrier 4: Fractal-Dimension Methods Insufficient

Abram-Lagarias show exceptional set is small (dim ≤ log₃φ), but:
- Small dimension ≠ empty
- Cannot force specific point λ = 1 to be non-exceptional

---

## 5. Where Erdős Sits Relative to Other Hard Problems

### Closer to Furstenberg ×2×3 than to Diophantine Sparsity

The dynamical reformulation:
- Action x ↦ 2x on Z₃
- 3-adic Cantor set (digits omitting 2) is fractal
- Erdős = orbit of 1 hits Cantor set only finitely often

This is archetypally **fractal/dynamical**, aligned with Furstenberg-type rigidity.

### A Weak Shadow of Normality Questions

If we could prove strong randomness for ternary digits of 2^n (positive frequency of digit 2, uniform distribution of blocks), Erdős would follow immediately.

But Roettger-Ren (2025) emphasize uniform distribution is unknown and Erdős is still open.

### Gel'fond Digit-Sum Problems: Partially Solved

Mauduit-Rivat proved Gel'fond conjecture about digit sums of primes.
That worked because there's averaging structure over primes.

Erdős is a **thin orbit** hitting a **thin fractal** - much less averaging.

---

## 6. What Could Plausibly Prove Erdős

### Option A: New Independence Principle

Something in the spirit of Furstenberg rigidity but strong enough to rule out a specific orbit hitting a specific Cantor set infinitely often.

### Option B: Couple Real and 3-adic Constraints

Control the "middle digits" - exactly what Lagarias says is missing.

### Option C: Carry Propagation Viewpoint

A global obstruction to avoiding digit 2 - more structural than modular pruning.

---

## 7. Key References

- **Dimitrov-Howe (2021)**: arXiv:2105.06440 - Bounded ones classification
- **Stoll slides (CIRM)**: cirm-math.fr - Counting bounds survey
- **Saye (2022)**: JIS - Verification to 5.9×10²¹
- **Bell (Numdam)**: Cobham-Mahler theory
- **Abram-Lagarias (EMS)**: 3-adic path-set fractals
- **Lagarias slides (Michigan)**: Real/3-adic combination problem
- **Roettger-Ren (2025)**: arXiv:2511.03861 - Digit frequency computations

---

## 8. Summary Table

| Method | What It Solves | Why It Fails for Erdős |
|--------|----------------|------------------------|
| Dimitrov-Howe | n ≤ 25 ones | n is unbounded |
| S-unit/Baker | Fixed sparsity | Can't uniformize over all n |
| Cobham | Automatic in 2 bases | Blocks, doesn't help |
| Mahler | Functional equations | No equation for 2^n |
| Dimension bounds | Size of exceptional set | Doesn't prove empty |
| Real + 3-adic | Leading + trailing digits | Can't combine for middle |
