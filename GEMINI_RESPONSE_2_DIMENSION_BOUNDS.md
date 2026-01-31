# Gemini Deep Research Report 2: Hausdorff Dimension Bounds

**Date:** January 30, 2026
**Prompt:** PROMPT_GEMINI_2_DIMENSION_BOUNDS.txt
**Type:** Technical Survey

---

## Executive Summary

This report provides an exhaustive technical survey of Hausdorff dimension bounds for the exceptional set in the Erdős problem. Key finding: the best explicit bound is **dim ≤ log₃φ ≈ 0.438**, but modern transversality theory (Shmerkin/Wu/Glasscock) strongly suggests **dim = 0**. However, proving dim = 0 does NOT automatically prove finiteness.

---

## 1. The Dynamical Framework

### 1.1 The 3-Adic Exceptional Set

Define:
$$E(\mathbb{Z}_3) = \{ \lambda \in \mathbb{Z}_3 : \lambda \cdot 2^n \in \Sigma_{3,\bar{2}} \text{ for infinitely many } n \}$$

where Σ_{3,2̄} is the 3-adic Cantor set (digits in {0,1}).

**Erdős Conjecture**: 1 ∉ E(Z₃)

**Lagarias Conjecture B**: E(Z₃) = {0}

### 1.2 Dimension Preservation

There is a continuous map ι: Z₃ → [0,1] that preserves Hausdorff dimension. So bounds in the 3-adic setting translate to real Cantor set dimensions.

**Trivial bound**: dim(Σ_{3,2̄}) = log₃2 ≈ 0.631

---

## 2. Lagarias (2005): First Non-Trivial Bounds

### 2.1 Approximation Sets

Lagarias introduced:
- E^(k)(Z₃) = {λ : at least k iterates hit Cantor set}
- E(Z₃) = ∩_{k≥1} E^(k)(Z₃)

### 2.2 Results

| Level | Bound | Significance |
|-------|-------|--------------|
| E^(1) | dim = log₃2 ≈ 0.631 | One hit doesn't reduce dimension |
| E^(2) | dim ≤ 1/2 = 0.500 | Two hits drops dimension significantly |

### 2.3 The Intersection Principle

The constraint λ ∈ E^(2) means:
$$\lambda \in \Sigma_{3,\bar{2}} \cap \frac{1}{M} \Sigma_{3,\bar{2}}$$

for some M = 2^k. Define:
$$C(1, M) = \Sigma_{3,\bar{2}} \cap \frac{1}{M} \Sigma_{3,\bar{2}}$$

**Lagarias proved**: If M is not a power of 3, then dim(C(1,M)) ≤ 1/2.

Multiplication by M "scrambles" the ternary expansion, destroying fractal alignment.

---

## 3. Path-Set Fractals and Automata

### 3.1 The Automata Construction

The intersection sets C(1, M) have rigid combinatorial structure described by finite automata.

**Key insight**: The set of valid ternary expansions for C(1, M) is recognized by a finite automaton that tracks the "carry" in multiplication.

States = carry values k_i
Transitions from equation: 3k_{i+1} + e_i = d_i·M + k_i

where d_i, e_i ∈ {0, 1}.

### 3.2 The Spectral Radius Formula

**Theorem**: For path-set fractal X_G defined by graph G with adjacency matrix A_G:
$$\dim_H(X_G) = \log_3 \rho(A_G)$$

where ρ(A_G) is the spectral radius (largest eigenvalue).

**Consequence**: Dimension bounds become linear algebra problems!

### 3.3 Algebraic Dimensions

Since ρ(A_G) is an eigenvalue of an integer matrix, dimensions are always log₃(β) for algebraic integers β.

This explains why bounds like log₃φ appear. The dimensions are discrete, not continuous.

---

## 4. The Golden Ratio Improvement (2015)

### 4.1 The Family N_k = 3^k + 1

Abram-Bolshakov-Lagarias analyzed:
$$C(1, N_k) = \Sigma_{3,\bar{2}} \cap \frac{1}{3^k+1} \Sigma_{3,\bar{2}}$$

**Result**: For all k ≥ 1:
$$\dim_H(C(1, N_k)) = \log_3 \phi \approx 0.438018$$

where φ = (1+√5)/2 is the Golden Ratio.

### 4.2 Why the Golden Ratio?

The constraint structure mimics the **Golden Mean Shift** - a subshift where "11" is forbidden.

The automaton contains a block resembling:
$$\begin{pmatrix} 1 & 1 \\ 1 & 0 \end{pmatrix}$$

Characteristic equation: λ² - λ - 1 = 0, yielding φ as dominant eigenvalue.

### 4.3 The Nesting Constant Γ

Define:
$$\Gamma = \inf_{M > 1} \dim_H(C(1, M))$$

**Current best bound**:
$$\dim_H(E(\mathbb{Z}_3)) \leq \Gamma^{**} \leq \log_3 \phi \approx 0.438$$

---

## 5. Bound Progression Summary

| Bound | Value | Source | Method |
|-------|-------|--------|--------|
| log₃2 | 0.631 | Trivial | Dimension of Cantor set |
| 1/2 | 0.500 | Lagarias (2005) | Pairwise intersection subadditivity |
| log₃φ | 0.438 | A-B-L (2015) | Automata for N_k = 3^k + 1 |
| → 0 | 0.000 | Conjectured | Infinite intersections |

---

## 6. Decimation and Interleaving

### 6.1 Decimation

Extract subsequence at arithmetic progression indices:
$$\psi_{j,n}(x_0 x_1 x_2 \ldots) = x_j x_{j+n} x_{j+2n} \ldots$$

Path-set fractals are closed under decimation.

### 6.2 Interleaving

Combine digit sequences:
$$Z = X * Y \iff z_{2k} \in X, z_{2k+1} \in Y$$

### 6.3 The Barrier

For N_k family, the path set decomposes via interleaving into Golden Mean shifts.

**Critical observation**: The dimension stabilizes at log₃φ as k → ∞. It does NOT decay to 0.

This suggests single families of intersections hit a barrier. Proving dim = 0 requires considering simultaneous intersection of MANY distinct families.

---

## 7. The Transversality Frontier (Shmerkin/Wu)

### 7.1 Furstenberg's Conjecture (Now Theorem)

For ×p-invariant set A and ×q-invariant set B (where log p / log q ∉ ℚ):
$$\dim_H(A \cap B) \leq \max(0, \dim_H(A) + \dim_H(B) - 1)$$

**Proved independently by Shmerkin (2019) and Wu (2020)**.

### 7.2 Application to Erdős

- dim(Σ_{3,2̄}) ≈ 0.63
- Orbit {2^n} has effective dimension 0
- Transversality formula: max(0, 0.63 + 0 - 1) = 0

**Heuristic strongly supports Conjecture B (dim = 0)**.

### 7.3 Dimension Drop Phenomenon

Unless there's an "exact overlap" of spectral structures, intersection dimensions drop significantly.

The automata results show dimension "sticks" at algebraic values for finite intersections. Proving dim = 0 requires the infinite limit.

---

## 8. Integer Fractal Theory (2024-2025)

### 8.1 Glasscock-Moreira-Richter

Developed rigorous theory of "fractal sets in the integers" with mass dimension paralleling Hausdorff dimension.

### 8.2 Integer Transversality Theorem

For ×r-invariant A and ×s-invariant B (r, s multiplicatively independent):
$$\dim(A \cap B) \leq \max(0, \dim A + \dim B - 1)$$

**This applies directly to integers, not just [0,1]!**

### 8.3 Implications

If the Erdős exceptional set had positive dimension in their framework, it would violate these theorems.

This provides the strongest theoretical evidence that E should be finite.

---

## 9. The Gap to Finiteness

### 9.1 The Critical Distinction

**dim = 0 does NOT imply finite!**

- Countable sets always have dim = 0
- But dim = 0 sets can be uncountable (e.g., Liouville numbers)

### 9.2 Current Status

- Best explicit bound: log₃φ ≈ 0.438 (strictly positive)
- Nesting constant Γ might be strictly positive
- If Γ > 0, intersection methods hit a barrier

### 9.3 Path Forward

Resolution likely requires combining:
1. **Probabilistic dimension drop** (Shmerkin/Wu/Glasscock) - to prove dim = 0
2. **Diophantine rigidity** (Baker's theorem) - to go from dim = 0 to finite

Must show the specific arithmetic of 2^n prevents it from landing in the "zero-dimensional dust" that remains.

---

## 10. Key Technical Contributions

### From Lagarias (2005)
- Reformulated as exceptional set problem
- Proved dim(E^(2)) ≤ 1/2 via subadditivity

### From Abram-Bolshakov-Lagarias (2015)
- Path-set fractal framework
- Spectral radius = dimension formula
- Golden Ratio bound log₃φ ≈ 0.438

### From Shmerkin/Wu (2019-2020)
- Proved Furstenberg's transversality conjecture
- Dimension drop for ×p, ×q invariant sets

### From Glasscock-Moreira-Richter (2024-2025)
- Integer fractal dimension theory
- Direct transversality in ℕ

---

## 11. Conclusion

The dimension bound trajectory:
```
0.631 → 0.500 → 0.438 → (conjectured 0)
```

The gap between 0.438 and 0 requires infinite intersection analysis.

The gap between dim = 0 and finiteness requires Diophantine rigidity.

**Current status**: Strong theoretical evidence for dim = 0, but no proof. Even stronger evidence for finiteness, but the final step requires novel synthesis of transversality and Diophantine methods.
