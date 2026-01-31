# Gemini Deep Research Report 3: Shrinking Targets and Borel-Cantelli

**Date:** January 30, 2026
**Prompt:** PROMPT_GEMINI_1_SHRINKING_TARGETS.txt
**Type:** Technical Survey

---

## Executive Summary

This report provides a comprehensive survey of shrinking target theory applied to the Erdős conjecture. **Key finding**: The problem is in the **convergence regime** where standard Borel-Cantelli applies without needing mixing. The measure of targets decays as (0.77)^n, so the sum converges. Additionally, log₃(2) has bounded irrationality measure (< 4.12), so it cannot "cheat" the probabilistic bound.

---

## 1. Classical Borel-Cantelli Lemmas

### 1.1 Convergence Case (First Lemma)

If Σ μ(A_n) < ∞, then μ(limsup A_n) = 0.

**Critical property**: This holds for ANY measure-preserving system, regardless of mixing or spectral type.

### 1.2 Divergence Case (Second Lemma)

If Σ μ(A_n) = ∞ AND events are independent, then μ(limsup A_n) = 1.

In dynamical systems, events are deterministically dependent, so this lemma cannot be applied directly.

### 1.3 Dynamical Borel-Cantelli Lemma (DBCL)

A system satisfies DBCL if the divergence conclusion holds despite deterministic dependence.

**Key distinction**:
- Mixing systems (hyperbolic, expanding): DBCL often holds
- Rotations: NOT mixing, correlations don't decay, DBCL fails generically

---

## 2. The Rotation Obstruction

### 2.1 Why Rotations Are Different

Irrational rotations are:
- Ergodic (invariant sets have measure 0 or 1)
- Dense orbits
- **NOT mixing** (correlations oscillate, don't decay)

This is the "Rotation Obstruction" - must rely on arithmetic properties of α, not mixing.

### 2.2 Fayad's Counterexamples

Fayad (2006) constructed shrinking targets where rotations hit infinitely often despite divergent measure sum - the DBCL fails.

### 2.3 When STP Holds for Rotations

**Kurzweil-Philipp Theorem**: For monotone shrinking balls, STP holds iff α is badly approximable.

**Key insight**: The threshold is ARITHMETIC (Diophantine type of α), not spectral.

---

## 3. Application to Erdős Conjecture

### 3.1 The Reformulation

The orbit {n·log₃(2) mod 1} must avoid the ternary Cantor set C₃ for 2^n to lack digit 2.

Target at step n: k-th level Cantor approximation where k ≈ n·log₃(2).

### 3.2 The Critical Calculation

**Measure of k-th level Cantor approximation**:
$$\mu(C_3^{(k)}) = 2^k \times 3^{-k} = (2/3)^k$$

**With k(n) ≈ n·log₃(2)**:
$$\mu(A_n) \approx (2/3)^{n \log_3 2} \approx (0.77)^n$$

### 3.3 Convergence Test

$$\sum_{n=1}^{\infty} \mu(A_n) \approx \sum_{n=1}^{\infty} (0.77)^n < \infty$$

**This is a convergent geometric series!**

### 3.4 Conclusion from Convergence BC

Since Σ μ(A_n) < ∞, by the Convergence Borel-Cantelli Lemma (which holds for ALL systems including rotations):

**For almost all α, the orbit hits the Cantor approximations only finitely often.**

---

## 4. The Specificity Problem

### 4.1 The Catch

Borel-Cantelli gives "almost all α" but log₃(2) is a specific constant.

**Question**: Could log₃(2) be in the measure-zero exception set?

### 4.2 How to "Cheat" the Bound

The only way for a specific α to violate generic probabilistic bounds is if α is **Liouville** (extremely well-approximable).

Liouville numbers have irrationality measure μ = ∞, allowing orbits to "stick" near rational approximants.

---

## 5. Diophantine Analysis of log₃(2)

### 5.1 Irrationality Measure Definition

μ(ξ) = inf{λ : |ξ - p/q| < 1/q^λ has only finitely many solutions}

| Number Type | Irrationality Measure |
|-------------|----------------------|
| Rational | μ = 1 |
| Typical irrational | μ = 2 |
| Algebraic irrational | μ = 2 (Roth) |
| Liouville | μ = ∞ |

### 5.2 The Key Result: Wu-Wang (2014)

**Theorem** (Wu-Wang): The irrationality measure of log₃(2) satisfies:
$$\mu(\log_3 2) < 4.1163$$

### 5.3 Implications

| Constant | Irrationality Measure |
|----------|----------------------|
| log₃(2) | < 4.12 |
| Liouville threshold | ∞ |

**log₃(2) is NOT Liouville!**

It is a Diophantine number - well-behaved, no extreme rational approximants.

---

## 6. Synthesis: Why the Conjecture Should Be True

### 6.1 The Convergence Regime Neutralizes Rotation Obstruction

The "Rotation Obstruction" (failure of mixing) only matters in the **divergence regime** where you need mixing to get DBCL.

In the **convergence regime** (Σ μ(A_n) < ∞), the first Borel-Cantelli lemma applies to ALL systems, including rotations.

### 6.2 The Arithmetic Validation

Even though we're asking about a specific α = log₃(2), not "almost all α":
- The only mechanism for specific α to escape generic bounds is being Liouville
- log₃(2) has bounded irrationality measure (< 4.12)
- Therefore log₃(2) cannot "cheat" the probabilistic bound

### 6.3 The Heuristic Conclusion

The orbit of log₃(2) is **statistically forced to exit the fractal constraints** of the Cantor set. The digit 2 must eventually appear.

---

## 7. Connection to Lagarias's Work

Lagarias (2009) proved the exceptional set of initial values λ (for which λ·2^n avoids digit 2 infinitely often) has Hausdorff dimension ≤ log₃(2).

This complements the rotation perspective: the set of exceptions is sparse/small.

---

## 8. Tseng's s-MSTP

Jimmy Tseng developed the s-exponent Monotone Shrinking Target Property.

For rotations, even when standard STP fails, the s-MSTP for s > 1 often holds.

This gives Hausdorff dimension bounds even when Lebesgue measure fails.

---

## 9. Key Quantitative Summary

| Quantity | Value | Source |
|----------|-------|--------|
| Measure decay rate | (0.77)^n | Exponential |
| Sum of measures | Convergent | Geometric series |
| Irrationality measure of log₃(2) | < 4.12 | Wu-Wang 2014 |
| Required for exception | μ = ∞ (Liouville) | |

---

## 10. Conclusion

The shrinking target framework provides strong theoretical support for the Erdős conjecture:

1. **Convergence regime**: μ(A_n) ≈ (0.77)^n, sum converges
2. **Universal BC applies**: First lemma holds for all systems including rotations
3. **Arithmetic validation**: log₃(2) is Diophantine, not Liouville
4. **No escape mechanism**: Cannot "cheat" the probabilistic bound

**The orbit is statistically forced to exit the Cantor set constraints.**

This is not a formal proof (that would require showing log₃(2) is not in the specific measure-zero exception set), but it provides overwhelming heuristic evidence from ergodic theory and Diophantine analysis.
