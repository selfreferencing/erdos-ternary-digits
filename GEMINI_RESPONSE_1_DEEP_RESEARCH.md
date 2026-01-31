# Gemini Deep Research Report 1: Log-Time Cancellation Structural Analysis

**Date:** January 30, 2026
**Prompt:** Level (c) Prompt 1 - Coherence Assessment
**Type:** Deep Research Report

---

## Executive Summary

This Gemini report provides a comprehensive structural analysis of the Erdős ternary digits conjecture through the lens of "log-time cancellation." The key finding: the search for such a theorem is **coherent but requires new mathematics** - specifically, a "Quantitative Transversality" theory that operates on finite timescales.

---

## 1. Introduction: The Architecture of an Open Problem

The Erdős conjecture (1979): For all sufficiently large n, the base-3 representation of 2^n must contain the digit 2.

**The log-time regime problem:**
- Target density: (2/3)^k at scale 3^k
- Available samples: O(k) values of n
- Discrepancy error: O(1/k)
- Required precision: O((2/3)^k)

**The Exponential Gap**: Error term 1/k becomes infinitely larger than target (2/3)^k as k → ∞.

---

## 2. Methodology of Mathematical Discovery

### 2.1 Coherence vs Category Error

A "log-time cancellation" theorem asking for error e^{-N} from N samples is generally a **category error** by information theory.

**However**: The search is coherent IF one postulates that log₃2 and the Cantor set possess a specific **arithmetic incompatibility**. The theorem would be about arithmetic orthogonality, not general equidistribution.

This parallels Measure Rigidity theorems: general ergodic measures can be anything, but measures invariant under ×2 AND ×3 are extremely restricted.

### 2.2 Distinguishing Unproven from False

Three heuristic tests:

1. **Heuristic Test**: Random model strongly suggests conjecture is true (expected hits finite and small)

2. **Obstruction Test**: If log₃2 were Liouville (very well-approximable), conjecture would likely be false. But computational evidence suggests log₃2 is Diophantine (badly approximable) - no obvious obstruction.

3. **Hierarchy of Difficulty**: Problems involving interaction of two multiplicative bases (2 and 3) are notoriously difficult (Furstenberg's ×2,×3 conjecture, Littlewood). Absence of theorem likely due to lack of tools, not falsity.

### 2.3 Evolution of Frameworks

Historical progression:
- **Weyl (1916)**: Qualitative equidistribution
- **Erdős-Turán (1940s)**: Quantitative discrepancy bounds
- **Roth/Schmidt (1960s-70s)**: Lower bounds on irregularity
- **Margulis/Furstenberg (1970s-90s)**: Homogeneous dynamics and rigidity

**"Log-Time Cancellation" is the next necessary evolution** - requiring synthesis of Diophantine approximation (handling "log-time" closeness) with fractal geometry (handling "missing digits" structure).

**Key insight**: This is asking for a more precise engine, not perpetual motion.

---

## 3. The Arithmetic Landscape

### 3.1 Logarithmic Scaling

- Number of ternary digits in 2^n: ⌊n log₃2⌋ + 1 ≈ 0.63n
- For fixed digit length k: typically 0, 1, or 2 values of n
- Density of samples: logarithmic relative to 2^n

### 3.2 The Exponential Gap (Precise)

| Quantity | Value |
|----------|-------|
| Target density | (2/3)^k |
| Sample size | O(k) |
| Discrepancy error | O(1/k) |
| Required precision | O((2/3)^k) |

As k → ∞, the error 1/k is infinitely larger than target (2/3)^k.

**This is the Arithmetic Void where current theorems fail.**

---

## 4. Failure of Classical Machinery

### 4.1 Weyl Sums

For irrational rotation x_n = nα:
```
|Σ e^{2πihnα}| ≤ 1/(2||hα||)
```

This depends on Diophantine properties of α. But for fractal targets:
- Characteristic function 1_{C₃} is not smooth
- Need Fourier series with frequencies up to 3^k resolution

### 4.2 Fourier Resonances of Cantor Set

The Cantor indicator has Fourier transform with "spikes" at powers of 3.

Error term involves Σ|1̂_{C₃}(h)|, which diverges or decays too slowly.

**The L¹ norm of the Dirichlet kernel for Cantor set grows exponentially with resolution, canceling out the exponential shrinkage of measure.**

This is the Exponential Gap: Weyl sums offer polynomial decay, but we face exponentially shrinking target.

---

## 5. The Ergodic Obstruction

### 5.1 Mixing vs Rigidity

**Critical distinction**: Irrational rotations are ergodic but NOT mixing.

- Mixing: μ(T^{-n}A ∩ B) → μ(A)μ(B) (asymptotic independence)
- Rotations: Zero entropy, no memory loss, perfect determinism

If rotations were mixing, Borel-Cantelli would apply easily. But rigidity means hitting times are governed by continued fraction expansion, not Poisson distribution.

### 5.2 Shrinking Target Property (STP)

**Key result**: Irrational rotations do NOT possess the general STP.

- **Fayad (2006)**: Proved there exist rotations and shrinking targets where Borel-Cantelli fails
- **Kurzweil (1955)**: Specific conditions for rotations, usually for interval targets of size 1/n

For exponential shrinking (2/3)^k, this places the problem in "hyperbolic" information regime where usually only positive-entropy systems satisfy BC.

**Danger**: The rigid orbit might miraculously "thread the needle" of the Cantor set if α has very specific arithmetic properties.

---

## 6. Measure Rigidity: The Hope for Resolution

### 6.1 Furstenberg's ×2,×3 Conjecture

**Statement**: The only non-atomic measure on [0,1] invariant under both T₂(x) = 2x mod 1 and T₃(x) = 3x mod 1 is Lebesgue measure.

**Relevance**:
- Powers of 2 = orbit of 1 under ×2
- Cantor set C₃ is invariant under ×3

The conjecture implies no "structured" way for ×2 orbit to hide inside ×3 invariant set. If they share no common structure, intersection should be finite.

### 6.2 Quantitative Rigidity and Finite Orbits

Lindenstrauss's work suggests "high entropy" actions (combined ×2, ×3) permit only Lebesgue measure.

**The "Log-Time Cancellation" we seek might be a corollary of "Quantitative Measure Rigidity"** - quantifying how fast an orbit under ×2 must become equidistributed with respect to ×3 structures.

### 6.3 Hausdorff Dimension Heuristic

- Cantor set dimension: s = log₃2 ≈ 0.631
- Orbit points: dimension 0
- Generic geometry: Sets with dim(A) + dim(B) < 1 typically have empty or finite intersection

This geometric intuition supports the conjecture: "thickness" of Cantor (0.63) + "thickness" of samples (0) is insufficient to force intersection in generic setting.

---

## 7. Heuristics and Computational Evidence

### 7.1 The Stochastic Model

If ternary digits are i.i.d. with P(digit = d) = 1/3:
```
E[# solutions] ≈ Σ (2/3)^{n log₃2} = Σ (0.77)^n < ∞
```

Geometric series converges rapidly. Expected number of digit-2-free powers is finite.

### 7.2 Computational Verification

**Saye (2022)**: Verified conjecture for n ≤ 2·3^45 ≈ 5.9×10²¹

No counterexamples beyond known cases (n = 0, 2, 8).

This absence of counterexamples where the heuristic predicts they should be most dense is strong evidence.

---

## 8. Structure of the Hypothetical Theorem

### 8.1 Proposed Form

**Hypothetical Theorem (Log-Time Cancellation / Quantitative Rigidity)**:

Let μ be a ×p-invariant measure on [0,1] with dimension s < 1. Let T_α(x) = x + α mod 1 where α = log_p(q) and p, q are multiplicatively independent.

Then there exists δ > 0 such that the number of visits of {nα}_{n=1}^N to the ε_N-neighborhood of the fractal support (where ε_N ~ p^{-N}) is bounded for sufficiently large N.

**Key**: This bounds extreme deviation probability, not average error, exploiting arithmetic non-resonance between rotation α and scaling p.

### 8.2 Framework Comparison Table

| Framework | Key Tool | Prediction | Obstruction |
|-----------|----------|------------|-------------|
| Probabilistic | Random Variables | TRUE | Ignores arithmetic structure |
| Diophantine | Weyl Sums | Inconclusive | Error O(1/N) too large for target (2/3)^N |
| Dynamical (STP) | Borel-Cantelli | Likely TRUE | Rotations not mixing; STP fails |
| Measure Rigidity | ×2,×3 Invariance | TRUE | Hard to quantify for finite orbits |
| **Log-Time Hypothesis** | **Quantitative Transversality** | **TRUE** | **Does not exist yet** |

---

## 9. Conclusion

The search for a "log-time cancellation theorem" is **coherent and necessary**.

The Erdős conjecture remains open because it sits in the **Arithmetic Void** - the gap between polynomial decay of discrepancy errors and exponential decay of fractal measures.

**Resolution will come from Quantitative Measure Rigidity** - a statement about exponential decay of correlations for "mixed-characteristic" observables.

Until such a tool is forged (combining Lindenstrauss's rigidity with effective Diophantine bounds), the conjecture remains a "heuristic certainty" rather than proven theorem.

**Bottom line**: "Log-Time Cancellation" is not perpetual motion (impossibility). It is asking for a **faster engine** - a level of arithmetic avoidance efficiency that nature seems to possess but current mathematics cannot capture.

---

## Key References from Report

- [On Two Conjectures Concerning Ternary Digits of Powers of Two](https://cs.uwaterloo.ca) - Waterloo
- [On a problem of Erdős (Hensel's lemma)](https://cirm-math.fr) - CIRM
- [MathOverflow: Status of digit 2 avoidance problem](https://mathoverflow.net)
- [Lagarias: arXiv:math/0512006](https://arxiv.org) - 3-adic framework
- [Shrinking target for non-autonomous systems](https://arxiv.org) - STP analysis
- [Rigidity of Multiparameter Actions](https://math.huji.ac.il) - Hebrew University
- [Dyadic approximation in Cantor's set](https://researchgate.net)
- [Ren-Roettger: arXiv:2511.03861](https://arxiv.org) - 2025 digit frequency paper
