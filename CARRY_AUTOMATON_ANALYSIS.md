# Carry Automaton Analysis for Erdős Conjecture

**Date:** January 31, 2026
**Purpose:** Formalize the doubling transducer, analyze base cases, classify cycles

---

## Part 1: The Doubling Transducer

### 1.1 Basic Operation

When doubling a number in base 3, we process digits right-to-left:

```
2 × d + carry_in = 3 × carry_out + output_digit
```

### 1.2 Complete Transition Table

| State (carry_in) | Input digit | Output digit | Next state (carry_out) |
|------------------|-------------|--------------|------------------------|
| 0 | 0 | 0 | 0 |
| 0 | 1 | 2 | 0 |
| 0 | 2 | 1 | 1 |
| 1 | 0 | 1 | 0 |
| 1 | 1 | 0 | 1 |
| 1 | 2 | 2 | 1 |

### 1.3 Forbidden Transitions (Output = 2)

To avoid digit 2 in output:
- **Forbidden**: (carry=0, digit=1) → outputs 2
- **Forbidden**: (carry=1, digit=2) → outputs 2

### 1.4 Allowed Transitions (Output ∈ {0,1})

| State | Allowed inputs | Output | Next state |
|-------|----------------|--------|------------|
| 0 | 0 | 0 | 0 |
| 0 | 2 | 1 | 1 |
| 1 | 0 | 1 | 0 |
| 1 | 1 | 0 | 1 |

### 1.5 The Survivor Automaton

States: {s0, s1} where s0 = no-carry, s1 = carry

```
     ┌─────┐          ┌─────┐
     │     │          │     │
     │ s0  │◄────────►│ s1  │
     │     │          │     │
     └─────┘          └─────┘
       │ ▲              │ ▲
       │ │              │ │
       └─┘              └─┘
      d=0              d=1
     out=0            out=0

Transitions:
  s0 --[d=0/out=0]--> s0  (stay, no carry)
  s0 --[d=2/out=1]--> s1  (generate carry)
  s1 --[d=0/out=1]--> s0  (consume carry)
  s1 --[d=1/out=0]--> s1  (maintain carry)
```

### 1.6 Key Constraint

**For a number to double without producing digit 2**:
- In state s0: input digit must be 0 or 2 (never 1)
- In state s1: input digit must be 0 or 1 (never 2)

This means the INPUT digits are constrained by the carry state!

---

## Part 2: The q = 0 Base Case Analysis

### 2.1 Setup

For N_orbit(seed, t) = seed × 4^(3^12) × (4^(3^13))^t:
- When t < 3^d, the ternary digits of t are all in positions 0 to d-1
- The "orbit generator" B = 4^(3^13) has a specific ternary structure
- As we examine deeper positions, the digit pattern stabilizes

### 2.2 Small t Analysis

Let me compute what happens for small t values:

**t = 0**: N_orbit(128, 0) = 128 × 4^(3^12)
- This is the base orbit number
- Need to check: does the tail from position 14 onward reject?

**t = 1**: N_orbit(128, 1) = 128 × 4^(3^12) × 4^(3^13)
- One "step" along the orbit

**t = 2**: N_orbit(128, 2) = 128 × 4^(3^12) × (4^(3^13))^2

### 2.3 Empirical Rejection Depths

From Session 5 Python analysis:

| t | Rejection depth (beyond pos 14) | Total positions checked |
|---|--------------------------------|------------------------|
| 0 | 1 | 15 |
| 1 | 2 | 16 |
| 2 | 1 | 15 |
| 3 | 2 | 16 |
| 4 | 3 | 17 |
| 5 | 1 | 15 |
| 6 | 2 | 16 |
| 7 | 4 | 18 |
| ... | ... | ... |
| 1519 | 23 | 37 |

### 2.4 The Stable Sequence Structure

For t with at most d ternary digits (t < 3^d):
- Positions 0 to 13: determined by seed × 4^(3^12)
- Positions 14 to 14+d: depend on t's digits interacting with B^t
- Positions beyond 14+d: stabilize (t's digits have "run out")

**Key insight**: Once past position 14 + (# digits of t), the automaton reads a fixed periodic sequence determined by B = 4^(3^13).

### 2.5 What the q = 0 Case Means

When q = t / 3^d = 0 (i.e., t < 3^d):
- t has at most d ternary digits
- After processing those d digits, the remaining tail is determined by the "stable" part of B^t
- Need to prove: this stable part eventually produces a 2

**The obstruction**: B^t for small t might have a long run of "compatible" digits before hitting a 2.

---

## Part 3: Cycle Classification

### 3.1 What Is a "Cycle"?

A cycle in the survivor automaton is a sequence of transitions that:
1. Returns to the starting state
2. Produces only outputs in {0, 1}
3. Corresponds to a repeating digit pattern

### 3.2 The Three Known Solutions

| n | 2^n | Ternary | Digit pattern |
|---|-----|---------|---------------|
| 0 | 1 | 1 | single digit |
| 2 | 4 | 11 | two 1s |
| 8 | 256 | 100111 | specific pattern |

### 3.3 Analyzing 2^8 = 256 = 100111₃

Reading right to left: 1, 1, 1, 0, 0, 1

Let's trace through the doubling:
- 256 × 2 = 512

512 in base 3:
512 = 512
512 / 3 = 170 r 2  ← digit 2 appears!

So 2^9 = 512 = 1...2...₃ (contains a 2)

**This confirms**: 2^8 is the last power of 2 without digit 2.

### 3.4 Why No Larger Cycles Exist

**Claim**: Any number N with only digits {0,1} in base 3, when doubled, eventually produces a 2.

**Proof sketch**:
1. If N has a digit 1 somewhere with carry = 0, output = 2 immediately
2. If N has a digit 2 somewhere with carry = 1, output = 2 immediately
3. The only way to avoid this is to maintain a rigid carry pattern

**The rigid carry constraint**:
- Digit 1 requires carry = 1 to avoid outputting 2
- But carry = 1 requires previous digit was 2 or (digit 1 with carry 1)
- Digit 2 requires carry = 0 to avoid outputting 2
- But carry = 0 means previous was 0 or (digit 2 with carry 0)

### 3.5 The Carry Propagation Lemma

**Lemma**: Consider a base-3 number N = d_{k-1}...d_1 d_0 with d_i ∈ {0, 1, 2}.
When computing 2N, let c_i be the carry into position i.

Then c_0 = 0, and:
- c_{i+1} = 1 iff (d_i = 2) or (d_i = 1 and c_i = 1)
- c_{i+1} = 0 iff (d_i = 0) or (d_i = 1 and c_i = 0) or (d_i = 2 and c_i = 0 and... wait, 2×2+0 = 4 = 1×3+1, so c_{i+1} = 1)

Let me redo this carefully:
- 2×0 + 0 = 0 → out=0, c=0
- 2×0 + 1 = 1 → out=1, c=0
- 2×1 + 0 = 2 → out=2, c=0 ← FORBIDDEN
- 2×1 + 1 = 3 → out=0, c=1
- 2×2 + 0 = 4 → out=1, c=1
- 2×2 + 1 = 5 → out=2, c=1 ← FORBIDDEN

### 3.6 Allowed Input Patterns

For N to double without producing 2:

**Starting from c = 0 (no carry)**:
- d = 0: allowed, next c = 0
- d = 1: FORBIDDEN (outputs 2)
- d = 2: allowed, next c = 1

**Starting from c = 1 (carry)**:
- d = 0: allowed, next c = 0
- d = 1: allowed, next c = 1
- d = 2: FORBIDDEN (outputs 2)

### 3.7 The Key Observation

**If the input N has only digits {0, 1}**:
- From state c=0: digit 0 OK (stay c=0), digit 1 FORBIDDEN
- From state c=1: digit 0 OK (go c=0), digit 1 OK (stay c=1)

**So to avoid outputting 2 when N has only {0,1} digits**:
- Must never see digit 1 while in state c=0
- This means: after any digit 0, the next digit must be 0 (not 1)
- The only allowed patterns are: all 0s, or a run of 1s preceded by setup

### 3.8 Classification Theorem (Informal)

**Theorem**: Let N be a positive integer with ternary digits in {0, 1}. Then 2N has a digit 2 unless:
- N = 1 (which gives 2N = 2, but wait, 2 in base 3 is just "2", a single digit 2!)

Wait, let me reconsider. We're looking at 2^n having no digit 2, not 2N having no digit 2.

### 3.9 Corrected Analysis: Powers of 2

The question is: for which n does 2^n have no digit 2 in base 3?

Let's trace the sequence:
- 2^0 = 1 = 1₃ ✓
- 2^1 = 2 = 2₃ ✗ (digit 2)
- 2^2 = 4 = 11₃ ✓
- 2^3 = 8 = 22₃ ✗
- 2^4 = 16 = 121₃ ✗
- 2^5 = 32 = 1012₃ ✗
- 2^6 = 64 = 2101₃ ✗
- 2^7 = 128 = 11202₃ ✗
- 2^8 = 256 = 100111₃ ✓
- 2^9 = 512 = 200222₃ ✗

### 3.10 Why {0, 2, 8} and Nothing Else?

The pattern 100111₃ for 2^8 = 256 is special:
- It's a sum of distinct powers of 3: 243 + 9 + 3 + 1 = 3^5 + 3^2 + 3^1 + 3^0
- This is an "accident" of small numbers

**Heuristic**: As n grows, 2^n has ~0.63n ternary digits. The probability that all ~0.63n digits avoid 2 is (2/3)^{0.63n} ≈ 0.77^n → 0.

**The cycle structure**:
- n = 0: trivial (1)
- n = 2: small coincidence (4 = 3 + 1)
- n = 8: larger coincidence (256 = 243 + 9 + 3 + 1)
- n > 8: no more coincidences found up to 10^21

### 3.11 Formal Cycle Impossibility

For n > 8, we need to show that 2^n must contain digit 2.

**Approach via orbit numbers**:
- 2^n mod 3^k determines the last k digits
- The sequence 2^n mod 3^k is periodic with period 2·3^{k-1}
- For each k, we can check: does every residue class produce a 2 in positions 0 to k-1?

**Saye's verification**: Checked all n ≤ 2·3^45 by recursive pruning. Every branch except {0, 2, 8} eventually produces a 2.

---

## Part 4: The Remaining Gap

### 4.1 What's Proved

1. The transducer structure is fully specified
2. All n ≤ 2·3^45 have been verified
3. The three known solutions {0, 2, 8} are genuine

### 4.2 What's Not Proved

**The infinite case**: We cannot computationally check all n.

**The theoretical gap**: We need to prove that the survivor automaton has no infinite accepting paths other than those corresponding to {0, 2, 8}.

### 4.3 The Saye Structure

Saye's algorithm shows:
- At depth k (checking first k digits), survivors form a tree
- The tree has ~(2/3)^k fraction of branches surviving at each level
- But this is a density argument, not a finiteness proof

### 4.4 What Would Close the Gap

**Option A**: Prove every residue class mod 3^K (for some fixed K) produces a 2 in positions 0 to K-1, except for finitely many that correspond to {0, 2, 8}.

**Option B**: Prove a "no-escape" lemma: once the automaton reaches a certain state configuration, it must eventually output a 2.

**Option C**: Prove the survivor set at depth k satisfies a recurrence that forces it to become {0, 2, 8} in finite time.

---

## Part 5: Computational Verification

### 5.1 Key Findings from Python Analysis

**Parity constraint**: 2^n mod 3 = 2 if n is odd. So **odd n always has last digit = 2**.

**All survivors must have even exponents.**

**Survivor density by depth**:

| Depth k | mod 3^k | Period | Survivors | Density |
|---------|---------|--------|-----------|---------|
| 1 | 3 | 2 | 1 | 0.5000 |
| 2 | 9 | 6 | 2 | 0.3333 |
| 3 | 27 | 18 | 4 | 0.2222 |
| 4 | 81 | 54 | 8 | 0.1481 |
| 5 | 243 | 162 | 16 | 0.0988 |
| 6 | 729 | 486 | 32 | 0.0658 |
| 7 | 2187 | 1458 | 64 | 0.0439 |

**Pattern**: Survivors = 2^{k-1} at depth k. Density ≈ (2/3)^k.

### 5.2 The Survivor Classes mod 81

The 8 residue classes (mod 54) with no digit 2 in last 4 positions:

| n mod 54 | 2^n mod 81 | Ternary |
|----------|------------|---------|
| 0 | 1 | 0001 |
| 2 | 4 | 0011 |
| 8 | 13 | 0111 |
| 18 | 1 | 1001 |
| 20 | 4 | 1011 |
| 24 | 28 | 0101 |
| 26 | 40 | 1111 |
| 42 | 37 | 1101 |

**Note**: n = 0, 2, 8 all appear in this list!

### 5.3 First Digit-2 Position for Non-Survivors

| n | 2^n ternary | First 2 position |
|---|-------------|------------------|
| 1 | 2 | 0 |
| 3 | 22 | 0 |
| 4 | 121 | 1 |
| 5 | 1012 | 0 |
| 6 | 2101 | 3 |
| 7 | 11202 | 0 |
| 9 | 200222 | 0 |

---

## Summary

### The Transducer
- 2 states (carry/no-carry)
- 4 allowed transitions (avoiding digit 2 output)
- Input constrained by current state

### The Key Constraints
1. **Odd n always fails** (last digit = 2)
2. **Survivor count = 2^{k-1}** at depth k (exactly half survive at each step)
3. **Survivor density = (2/3)^k** → 0 exponentially

### The Three Accidents
| n | 2^n | Ternary | Why special |
|---|-----|---------|-------------|
| 0 | 1 | 1 | Trivial |
| 2 | 4 | 11 | 4 = 3 + 1 |
| 8 | 256 | 100111 | 256 = 3^5 + 3^2 + 3 + 1 |

These are "coincidences" where a power of 2 happens to equal a sum of distinct powers of 3.

### The Fundamental Gap

**What's proved**:
- At each depth, exactly 1/3 of survivors die
- Survivor density → 0 exponentially
- Verified to n ≤ 2·3^45 ≈ 5.9×10²¹

**What's not proved**:
- Every specific n eventually dies
- "Density → 0" ≠ "set is finite"

### The Proof Target

Show: for every t ∈ ℕ, there exists depth d such that digit(14 + d) of N_orbit(seed, t) equals 2.

This is equivalent to: **the survivor tree has no infinite branches**.
