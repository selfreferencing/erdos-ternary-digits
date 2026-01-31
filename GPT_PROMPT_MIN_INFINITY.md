# GPT Pro Prompt: Prove min(survivors) → ∞

## The Problem

We're working on the Erdős ternary digits conjecture: the only n ≥ 0 such that 2^n has no digit 2 in base 3 are n = 0, 2, 8.

We've reduced this to proving that a certain survivor tree has no infinite branches.

## The Setup

Define the **survivor set at depth k**:
```
S_k = {n mod (2·3^{k-1}) : 2^n mod 3^k has no digit 2}
```

**Key facts we've established**:

1. **Parity constraint**: If n is odd, then 2^n ≡ 2 (mod 3), so the last digit is 2. Therefore all survivors have even exponents.

2. **Survivor count**: |S_k| = 2^{k-1} exactly. The count doubles at each depth.

3. **Density decay**: |S_k| / (2·3^{k-1}) = (2/3)^{k-1} / 2 → 0 exponentially.

4. **Empirical min growth**: The minimum element of S_k (viewed as a natural number) grows:
   ```
   k=1: min=0
   k=2: min=0 (both 0 and 2 survive)
   k=3: min=0 (0, 2, 8 survive, plus more)
   k=4: min=0
   ...eventually min starts growing...
   k=15: min=1347
   k=16: min=1519
   k=23: min=1519 still (the "champion")
   ```

5. **The j=0 child kill frequency**: At each depth, approximately 1/3 of survivor nodes have their j=0 child killed (the residue class r becomes r at the next level, but the k+1-th digit is 2). When this happens, the minimum jumps by ~3^k.

## The Key Lemma We Need

**Lemma (min → ∞)**:
```
lim_{k→∞} min(S_k) = ∞
```

Equivalently: For every N ∈ ℕ, there exists K such that for all k ≥ K, every element of S_k is > N.

**Why this suffices**: If min(S_k) → ∞, then for any fixed n, there exists k such that n < min(S_k), meaning n ∉ S_k, meaning 2^n has a digit 2 in its first k ternary digits.

## The Algebraic Structure

The survivors at depth k are determined by:
```
2^n mod 3^k ∈ {m : m has no digit 2 in base 3, m < 3^k}
```

The map n ↦ 2^n mod 3^k is periodic with period 2·3^{k-1} (since 2 is a primitive root mod 3^k for k ≥ 1).

When going from depth k to k+1:
- Each survivor r ∈ S_k spawns 3 candidate children: r, r + period_k, r + 2·period_k
- Exactly 2 of these 3 children survive (on average)
- The child that dies is determined by whether the (k+1)-th digit of 2^n mod 3^{k+1} equals 2

## The Equidistribution Property

We proved (via Lifting the Exponent):
- For any survivor r at depth k, the (k+1)-th digit of its three children cycles through {0, 1, 2} in some order
- This is a perfect permutation: exactly one child has digit 0, one has digit 1, one has digit 2
- The child with digit 2 dies

This means the survivor tree is "perfectly balanced" at each level: every node loses exactly one of its three children.

## What Needs to Be Proved

**Approach 1: Direct min→∞**

Show that the j=0 child (residue class r remaining as r) is killed infinitely often at the minimum.

When r is the minimum survivor at depth k, and r's j=0 child is killed, the new minimum at depth k+1 jumps to at least r + 2·3^{k-1} (the period).

**Approach 2: Structural obstruction**

Show that staying at a fixed residue class forever is impossible. This requires the (k+1)-th digit at that residue class to be 0 or 1 for all k, but the digits cycle through {0,1,2} as k varies...

Wait, this is the key! Let me think more carefully.

For a fixed n, consider the sequence of digits:
- digit_1(2^n) = 2^n mod 3
- digit_2(2^n) = (2^n / 3) mod 3
- digit_k(2^n) = (2^n / 3^{k-1}) mod 3

For n to survive all depths, we need digit_k(2^n) ≠ 2 for all k ≤ L(n) where L(n) is the number of ternary digits of 2^n.

**The question**: For fixed n, why can't all ~0.63n digits avoid 2?

## Possible Proof Strategies

### Strategy A: Probabilistic lower bound on digit 2 appearances

Show that the number of positions where digit = 2 is at least cn for some c > 0, with probability 1 over... wait, this is deterministic, not probabilistic.

### Strategy B: Algebraic periodicity forces digit 2

The sequence 2, 4, 8, 16, 32, ... mod 3^k is periodic. Perhaps the structure of this period forces digit 2 to appear?

### Strategy C: The min-growth argument

Track the minimum survivor. Show:
1. The minimum can only increase (by the period) or stay the same
2. It cannot stay the same forever (the j=0 child is killed infinitely often)
3. Therefore min → ∞

For (2), we need: for the minimum survivor r at depth k, the j=0 child (which corresponds to n ≡ r mod period_k) has its (k+1)-th digit equal to 2 infinitely often.

This is a statement about the specific arithmetic of 2^r mod 3^{k+1}.

## Your Task

Please attempt to prove the Lemma (min → ∞) using any of the strategies above or a new approach.

**Deliverables**:
1. A proof sketch (can have gaps if necessary)
2. Identification of the key sub-lemma that would close the argument
3. If the proof is blocked, a clear statement of what additional property would suffice

## Notation Summary

- S_k = survivor set at depth k (residue classes mod 2·3^{k-1})
- |S_k| = 2^{k-1}
- period_k = 2·3^{k-1}
- digit_k(m) = k-th ternary digit of m (from right, 1-indexed)
- For n to survive depth k: digit_j(2^n) ≠ 2 for all j ≤ k
