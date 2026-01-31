# GPT Pro Response 1: min(S_k*) → ∞ Proof Strategy

**Date:** January 31, 2026
**Prompt:** GPT_PROMPT_MIN_INFINITY.md
**Type:** Targeted Proof Attempt

---

## Key Correction: The Lemma Needs S_k*

With the literal definition of S_k, we always have 0 ∈ S_k (because 2^0 = 1 has no digit 2), so min(S_k) = 0 for every k. Likewise 2, 8 ∈ S_k for all k.

**Corrected lemma (nontrivial min → ∞):**

Let S_k* := S_k \ {0, 2, 8} (remove the three known infinite branches). Then:
```
min(S_k*) → ∞
```

This is equivalent to "there is no other fixed integer exponent surviving all depths", i.e., the Erdős ternary digits conjecture.

---

## 1) Lemma A: First Post-Valuation Digit

Because odd exponents die immediately (last ternary digit = 2), write n = 2m and study:
```
2^n = 4^m = (1+3)^m
```

Let v := v₃(m) and write m = 3^v u with 3 ∤ u.

### Lemma A

For m ≥ 1, with v = v₃(m) and m = 3^v u:
```
4^m ≡ 1 + 3^{v+1}u (mod 3^{v+2})
```

Equivalently, in ternary digits:
- digit₁(4^m) = 1
- digit₂, ..., digit_{v+1}(4^m) = 0
- digit_{v+2}(4^m) ≡ u (mod 3)

### Proof Sketch

Expand (1+3)^m:
```
(1+3)^m = 1 + 3m + Σ_{j≥2} C(m,j) 3^j
```

- The term 3m has exact 3-adic valuation v+1
- For j = 2: C(m,2)·3² has valuation ≥ v+2
- For j ≥ 3: 3^j contributes at least 3³, and C(m,j) has ≥ v-1 factors of 3
- So modulo 3^{v+2}: 4^m ≡ 1 + 3m = 1 + 3^{v+1}u ∎

### Consequence for j=0 Child Kill

The event "the j=0 lift dies at the next level" occurs when the next digit revealed is 2.

**Lemma A says**: If the least significant nonzero ternary digit of m is 2 (i.e., u ≡ 2 mod 3), then digit_{v+2}(4^m) = 2, so the exponent dies at depth k = v+2.

This makes rigorous the "~1/3 j=0 kills" heuristic.

---

## 2) Min-Growth Strategy

Working with S_k* (nontrivial survivor sets), define m_k := min(S_k*).

1. **Monotonicity:** m_{k+1} ≥ m_k

2. **Big jumps when the min's j=0 lift dies:** If m_k ∈ S_k* but m_k ∉ S_{k+1}* via the j=0 lift, then m_{k+1} must jump by ~3^k, **unless** there's another survivor in [m_k, m_k + 2·3^{k-1}) whose j=0 lift survives.

3. **What Lemma A gives:** A deterministic, digit-theoretic certificate for when a fixed exponent's j=0 lift must die.

**The min-growth program reduces to:** Show you can't keep finding small survivors whose least-nonzero ternary digit is always 1, without eventually triggering a forbidden digit deeper.

---

## 3) The Key Sub-Lemma (The Crux)

**Key Sub-lemma (iterated digit readout / no ultimately-zero path):**

Fix an integer m > 4. Consider the 3-adic valuation tower m = 3^v u, 3 ∤ u, and expand u in base 3:
```
u = u₀ + 3u₁ + 3²u₂ + ⋯, u_i ∈ {0, 1, 2}
```

Then there exists some t ≥ 0 such that digit_{v+2+t}(4^m) = 2.

**If you can prove this**, then every m > 4 dies at some finite depth, hence min(S_k*) → ∞.

**Tree version:** For every node corresponding to an integer exponent n ∉ {0, 2, 8}, there is some depth at which the j=0 child is killed.

---

## 4) Higher-Order Blueprint via 3-adic Log/Exp

Since 4 = 1+3 ∈ 1+3ℤ₃, define L := log(4) ∈ 3ℤ₃.

Then 4^m = exp(mL) in ℤ₃.

Write m = 3^v u with 3 ∤ u. Then mL has valuation v+1.

For fixed precision t, if v is large compared to t:
```
4^m ≡ 1 + 3^{v+1}(u · λ_t) (mod 3^{v+1+t})
```
where λ_t is the unit L/3 reduced mod 3^t.

**Interpretation:** The block of t ternary digits of 4^m immediately after the first v+1 low digits is (up to a fixed unit multiplier) the block of t digits of u in ℤ/3^t ℤ.

"Those t digits avoid 2" becomes:
```
u·λ_t ∈ C_t ⊂ ℤ/3^t ℤ
```
where C_t is the length-t "digits in {0,1}" Cantor set mod 3^t.

**The hard global step:** Show that ∩_t λ_t^{-1}C_t contains **no ordinary integer u** other than those corresponding to m = 1, 4.

This is Lagarias's formulation: intersections of multiplicative translates of the 3-adic Cantor set.

---

## 5) Three "Would-Suffice" Properties

### (A) Tree-native closing property

**Uniform kill of bounded integers:** For every N there is a depth K(N) such that every integer exponent n ≤ N, n ∉ {0, 2, 8}, has the j=0 child killed at or before depth K(N).

This is literally equivalent to min(S_k*) → ∞.

### (B) Finite-state / automaton sufficiency (carry transducer)

Encode multiplication by 4 = 11₃ as digitwise addition x + 3x with carry. Restrict to the shift space {0,1}^ℕ.

If you can build the finite directed graph of admissible carry states and prove that the only eventually-all-zero digit sequences in the resulting inverse-limit (corresponding to ordinary integers) are the three known ones, you're done.

### (C) Quantitative mixing / discrepancy sufficiency

There exists δ > 0 and k₀ such that for all integers n ≥ k₀, among the first ⌊cn⌋ ternary digits of 2^n (with c = log₃2), at least a δ-fraction are equal to 2.

This would force every large exponent to contain a 2.

---

## 6) What Lemma A Gives "For Free"

- A closed-form digit certificate for a whole infinite family of exponents that must die at a specific depth
- Explains why j=0 child is killed with stable positive frequency
- Suggests a program: compute higher "post-valuation digits" via higher-precision log/exp or binomial valuation bookkeeping
- The whole conjecture becomes: the infinite constraint system has only three integer solutions

---

## Context Note

The conjecture is still open, verified computationally to n ≤ 2·3^45 ≈ 5.9×10²¹ (Saye 2022). The "key sub-lemma" above is genuinely the crux.

---

## References

1. Lagarias: [arXiv:math/0512006](https://arxiv.org/abs/math/0512006)
2. Saye (2022): [JIS Paper](https://cs.uwaterloo.ca/journals/JIS/VOL25/Saye/saye3.pdf)
