# Gemini Response 5: Comprehensive Computational Analysis

**Date:** January 31, 2026
**Prompt:** PROMPT_GEMINI_4_COMPUTATIONAL.txt
**Type:** Comprehensive Technical Survey

---

## Executive Summary

Exhaustive survey of computational verification and heuristic evidence. Confirms conjecture verified to n ≤ 2·3^45 ≈ 5.9×10²¹ (Saye 2022). Probabilistic heuristic gives convergent sum (ratio ~0.77), predicting finite exceptions with near-certainty. Investigates "Spencer proof" claim and finds it unsubstantiated. The barrier is carry propagation chaos and p-adic transcendence.

---

## 1. The Conjecture

**Statement**: For every integer n > 8, the base-3 representation of 2^n contains the digit 2.

**Exceptional set**: E = {n ∈ N : 2 ∉ digits((2^n)₃)}

**Erdős conjecture**: E = {0, 2, 8}

### The Known Exceptions

| n | 2^n | Base-3 | Digits Used |
|---|-----|--------|-------------|
| 0 | 1 | 1₃ | {1} |
| 2 | 4 | 11₃ | {1} |
| 8 | 256 | 100111₃ | {0, 1} |

For n = 8: 256 = 243 + 9 + 3 + 1 = 3^5 + 3^2 + 3^1 + 3^0

### The Sloane Conjecture (Related)

S = {n ∈ N : 0 ∉ digits((2^n)₃)} = {0, 1, 2, 3, 4, 15}

Largest: 2^15 = 32768 = 1122221122₃

---

## 2. Computational Verification History

| Year | Author | Verified Up To | Approximate Value |
|------|--------|----------------|-------------------|
| 1978 | Gupta | n ≤ 4,373 | ~10³ |
| 1991 | Vardi | n ≤ 2·3^20 | ~7×10⁹ |
| 2022 | Saye | n ≤ 2·3^45 | ~5.9×10²¹ |

**Scale of Saye's verification**: Checking sequentially at 1 billion/second would take ~200,000 years.

---

## 3. Saye's Algorithm: Technical Details

### Core Insight: Periodicity

The sequence of powers of 2 modulo 3^k is periodic with period u_k = 2·3^{k-1}.

The last k ternary digits of 2^n repeat with this period.

### Algorithm: Depth-First Search with Pruning

1. **Initialization**: Start with small exponent (n = 0)

2. **Extension**: Attempt to extend valid sequence of trailing digits by one position

3. **Branching**: For valid suffix of length k (exponent j), consider three extensions:
   - n₁ = j
   - n₂ = j + u_k
   - n₃ = j + 2u_k

4. **Pruning**: Calculate (k+1)-th digit for each candidate
   - If digit is forbidden (2): prune branch
   - If digit is allowed (0 or 1): recurse to depth k+1

### Implementation

- **Modulus**: Calculations mod 3^54
- **Representation**: Numbers as three "super-digits" in base 3^18 using 64-bit integers
- **Fallback**: If target digit not in first 54 digits, use exponentiation-by-squaring

### Output: Record Breakers

- **A351927**: Smallest 2^n where last k ternary digits contain no 0
- **A351928**: Smallest 2^n where last k ternary digits contain no 2

These quantify "persistence" of missing digits. All sequences eventually terminate.

---

## 4. The Probabilistic Heuristic

### The Randomness Assumption

Ternary digits of 2^n behave like independent random variables uniform on {0, 1, 2}.

Justified by: log₃(2) is irrational → sequence n·log₃(2) mod 1 is equidistributed.

### The Calculation

**Number of ternary digits**: D(n) = ⌊n·log₃(2)⌋ + 1 ≈ 0.631n

**Probability digit ≠ 2**: 2/3

**Probability all D(n) digits ≠ 2**: P_n = (2/3)^{D(n)} ≈ (2/3)^{0.631n}

**Simplification**: P_n ≈ (0.7737)^n

### Expected Number of Exceptions

$$E = \sum_{n=1}^{\infty} P_n \approx \sum_{n=1}^{\infty} (0.7737)^n$$

This is a **convergent geometric series** with ratio r ≈ 0.77 < 1.

$$\sum_{n=1}^{\infty} r^n = \frac{r}{1-r} \approx 3.4$$

### Interpretation

- By n = 60: probability < 10^{-6}
- By n = 1000: probability effectively zero
- **Borel-Cantelli** (heuristic): with probability 1, only finitely many exceptions

### Comparison with Other Conjectures

| Problem | Probability Decay | Sum Behavior | Prediction |
|---------|-------------------|--------------|------------|
| Twin Primes | ~1/ln(n) | Diverges | Infinitely many |
| Erdős Ternary | ~c^n | Converges | Finitely many |

The exponential convergence gives much higher confidence than for twin primes.

---

## 5. Empirical Digit Frequency Analysis

### Ren-Roettger Study (2025)

Computed full ternary expansions for n ≤ 10^6 (over 315 billion ternary digits).

### Results at n = 10^6

| Digit | Observed | Expected |
|-------|----------|----------|
| 0 | 33.333041% | 33.333333% |
| 1 | 33.333576% | 33.333333% |
| 2 | 33.333382% | 33.333333% |

Deviations ~10^{-5}, consistent with Law of Large Numbers.

### Higher-Order Statistics

| Block Type | Expected | Observed Range |
|------------|----------|----------------|
| 2-strings | 1/9 ≈ 11.11% | 11.1108% - 11.1111% |
| 3-strings | 1/27 ≈ 3.7037% | Similarly precise |

**Implication**: Strong evidence that log₃(2) is a **normal number** in base 3.

### Leading vs Internal Digits

- **Leading digits**: Follow Benford's Law (digit 1: ~63%, digit 2: ~37%)
- **Internal digits**: Rapidly converge to uniform distribution

---

## 6. Structural Patterns

### The Parity Constraint

**Crucial observation**:
- n even: 2^n ≡ 1 (mod 3) → last digit is 1
- n odd: 2^n ≡ 2 (mod 3) → last digit is **2**

**Consequence**: All counterexamples must have **even exponents**.

This explains why {0, 2, 8} are all even. Odd powers automatically contain digit 2.

### The "Stairs" Pattern (Aliyev 2023)

When ternary representations stacked vertically, diagonal bands of identical digits emerge.

**Mechanism**: Visual manifestation of periodicity mod 3^k

**Implication**: Arbitrarily long runs of any digit occur in trailing positions. The digits cycle through all possibilities.

---

## 7. The "Spencer Proof" Investigation

### Search Results

- **Joel Spencer**: Famous Erdős collaborator, works on discrepancy theory. No record of claiming ternary digits proof.

- **"Carry-Exclusion"**: Term appears in campus firearms policies, not mathematics.

- **"Salem-Spencer sets"**: Related to arithmetic progressions, different Erdős area.

### Verdict

**The "Spencer proof" is a phantom citation** - likely misinterpretation of Joel Spencer's discrepancy work or confusion with Salem-Spencer sets.

**The problem remains OPEN.** No accepted proof exists.

---

## 8. The Real Theoretical Barrier: Carry Propagation

### The Mechanism

When computing 2^{n+1} from 2^n in base 3:

| d_i | 2 × d_i | Result | Carry |
|-----|---------|--------|-------|
| 0 | 0 | 0 | 0 |
| 1 | 2 | 2 | 0 |
| 2 | 4 = 11₃ | 1 | 1 |

### The Problem

Carries allow information to flow from position i to position i+1.

This flow is **chaotic** - a single carry can trigger cascades (avalanche effect).

### The Barrier

To prove the conjecture, must show carry propagation is sufficiently complex to prevent digits from staying in {0, 1}.

**We lack tools to quantify this mixing rigorously for specific integers.**

---

## 9. The Lagarias 3-adic Approach

### Setup

- **Map**: T: x ↦ 2x on Z₃
- **Exceptional Set E**: All λ ∈ Z₃ such that trajectory λ, 2λ, 4λ, ... always omits digit 2

### Results

Lagarias proved: dim_H(E) ≤ log₃(2) ≈ 0.631

**Meaning**: "Vast majority" of 3-adic integers are not counterexamples.

### The Gap

This is a **metric result** (about "almost all" numbers).

It does NOT tell us whether the specific integer λ = 1 lies in E or not.

**Proving specific integers avoid fractal exceptional sets is notoriously difficult.**

---

## 10. Related Problems

### Powers of 2 in Base 10

- Missing digit phenomenon disappears faster (base larger)
- Probability decays as (9/10)^{0.3n}
- Conjecture: 2^86 is largest power of 2 missing digit 0 in base 10

### Powers of 3 in Base 2

- Inverse of Erdős problem
- Binary digits of 3^n believed uniformly distributed
- No proof exists

### General Case: p^n in Base q

For multiplicatively independent p, q: base-q digits of p^n eventually include all digits.

Erdős case (p=2, q=3) is "hardest" elementary case since q=3 is smallest non-trivial base.

---

## 11. Conclusion

### What We Know

| Evidence Type | Certainty Level |
|---------------|-----------------|
| Heuristic (convergent sum) | Near-absolute |
| Computational (to 10²¹) | Complete verification |
| Statistical (digit frequencies) | Perfect uniformity |

**Probability of counterexample beyond n = 1000**: < 10^{-100}

### What We Don't Know

- A proof
- Why 256 is special
- How to bridge metric results to specific integers

### The Path Forward

Not better computers, but breakthrough in **p-adic transcendence theory** - showing arithmetic structure of integer 1 is incompatible with fractal structure of "missing digit" sets.

---

## Key References

- **Saye (2022)**: JIS, arXiv:2202.13256 - Verification to 5.9×10²¹
- **Lagarias (2009)**: arXiv:math/0512006 - 3-adic framework
- **Ren-Roettger (2025)**: arXiv:2511.03861 - Digit frequencies
- **Dimitrov-Howe (2021)**: arXiv:2105.06440 - Bounded ones
- **Aliyev (2023)**: NNTDM - Stairs patterns
- **OEIS A351927, A351928**: Record breakers
