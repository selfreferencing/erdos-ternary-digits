# GPT Response 7 (55B): Shrinking Target Literature Survey

**Date:** January 30, 2026
**Prompt:** Detailed shrinking-target / Borel-Cantelli literature for rotations

---

## Core Finding: Why Existing STP/BC Tools Fail

The standard Shrinking Target Property (STP) and Borel-Cantelli (BC) theorems are designed for **single-interval targets**, not the exponentially many components arising in the Erdős problem.

### The Component Explosion Problem

At depth d, the target set S_d (ternary expansions avoiding digit 2 in first d positions) has:
- **9^d separate intervals** (each of width 3^{-d})
- Total measure (2/3)^d

Standard discrepancy bounds handle unions of m intervals with cost O(m). When m = 9^d, this destroys any useful bound.

---

## Why Koksma-Type Bounds Blow Up

### The Koksma Inequality

For f of bounded variation:
```
|S_N(f) - N∫f| ≤ Var(f) · D_N
```

where D_N is the discrepancy.

### Applied to Erdős Target

- f = 1_{S_d} (indicator of d-digit constraint set)
- Var(1_{S_d}) ~ 9^d (crossing 9^d boundary pairs)
- Even with perfect D_N = O(log N / N), the bound is:
  ```
  9^d · log N / N
  ```
- For d ~ c·log N, this gives no useful bound

**Conclusion**: Koksma-based approaches are fundamentally blocked.

---

## What's Missing in Standard Theorems

### Existing MSTP Results (Fayad, Kim, etc.)

- Target sequence: shrinking balls B(x, r_n)
- Threshold: Σ r_n < ∞ → finitely many hits (a.e.)
- Works for **single connected target** at each step

### What Erdős Needs

- Target at step d: **disconnected set** with 9^d components
- Each component is tiny (3^{-d}) but there are exponentially many
- Need to track orbit visiting ANY of 9^d pieces

### The Structural Gap

No existing theorem handles:
- Exponentially many target components
- Lattice structure (3-adic arithmetic)
- Specific orbit (not generic x)

---

## Most Promising Conceptual Pivot

### Fourier / Exponential-Sum Route

Instead of geometric/discrepancy methods, exploit:
1. **Digit-cylinder structure**: Target is defined by digit constraints
2. **Exponential sums**: Characters of Z/3^d Z
3. **Cancellation from α = log₃2**: Irrational rotation gives oscillation

### What This Would Require

- Nontrivial bounds on sums like:
  ```
  Σ_{n≤N} 1_{digit_j(2^n) ≠ 2}
  ```
- This is related to Gel'fond problems on digit sums
- Known partial results exist but don't reach finiteness

### Why It Might Work

The Fourier approach doesn't pay for 9^d components separately. Instead:
- Indicator 1_{S_d} has Fourier expansion with 3-adic structure
- Orbit sums may cancel due to equidistribution properties
- Need to overcome resonance (3 | 3 exactly)

---

## Weaker Provable Results

### What Might Be Achievable

1. **Density bounds**: #{n ≤ N : 2^n ∈ S_d} = o(N) for each d
   - Already known (N(X) ≪ X^{log₃2})

2. **Dimension bounds on parameters**: dim(E) ≤ c < 1
   - Already achieved (c ≈ 0.438)

3. **Conditional results**: "If [Diophantine property], then finite"
   - Would clarify what's really needed

### What Seems Out of Reach

- Finiteness for the specific orbit 2^n
- Any statement about λ = 1 specifically

---

## Offer: Fourier Route Sketch

GPT offered to sketch in detail what the Fourier route would look like:
- Specific exponential sums to bound
- Known partial results to leverage
- Where the key obstruction lies

---

## Key Takeaway

The standard dynamical systems toolkit (shrinking targets, Borel-Cantelli, discrepancy) is fundamentally mismatched to the Erdős problem because:

1. **Component explosion**: 9^d pieces vs single target
2. **Arithmetic resonance**: 3-adic lattice structure blocks Fourier decay
3. **Specific orbit**: Need λ = 1, not generic behavior

The most promising pivot is Fourier/exponential-sum methods that exploit digit-cylinder structure rather than geometric properties.
