# GPT Pro Response 2: Carry Automaton Approach

**Date:** January 31, 2026
**Prompt:** GPT_PROMPT_MIN_INFINITY.md
**Type:** Targeted Proof Attempt (Alternative Route)

---

## Same Correction: Need S_k*

As stated, `min(S_k) → ∞` cannot hold because n = 0 satisfies the digit condition for every k. The correct statement:

> **Lemma (nontrivial min → ∞):**
> lim_{k→∞} min(S_k \ {0, 2, 8}) = ∞

This is exactly the "no new infinite branches" statement.

---

## Why the Lemma = "No New Infinite Branch"

For fixed n and sufficiently large k, the modulus 2·3^{k-1} exceeds n, so "n mod (2·3^{k-1})" is just n. Hence for large k:

```
n ∈ S_k ⟺ first k ternary digits of 2^n avoid 2
```

If some n ∉ {0, 2, 8} survived all depths, the nontrivial minimum would be ≤ n forever. Conversely, if min stays bounded, some n ≤ N survives all depths → new infinite branch.

---

## The Carry-Automaton Obstruction for ×4 in Base 3

### Step 1: Reduce to Powers of 4

By parity constraint, any nontrivial survivor exponent is even: n = 2m. Then:
```
2^n = 2^{2m} = 4^m
```

**Conjecture becomes**: Classify integers m ≥ 0 for which 4^m has only digits {0, 1} in ternary.

**Known solutions**: m = 0, 1, 4 (giving n = 0, 2, 8)

### Step 2: Model ×4 as "Add a Shifted Copy"

In base 3, 4 = 11₃ = 1 + 3. For any X:
```
4X = X + 3X
```
(add X to itself shifted left by one ternary digit)

Write:
```
X = Σ x_i · 3^i, x_i ∈ {0, 1, 2}
4X = Σ y_i · 3^i, y_i ∈ {0, 1, 2}
```

Let c_i ∈ {0, 1, 2} be the carry into position i (with c_0 = 0). Then digit-by-digit:
```
x_i + x_{i-1} + c_i = y_i + 3·c_{i+1}  (where x_{-1} := 0)
```

### Step 3: The 9-State Transducer

**Constraint for "no digit 2 in output"**: require y_i ∈ {0, 1} for all i.

Since x_i + x_{i-1} + c_i ranges from 0 to 6, the **forbidden sums** that force y_i = 2 are:
```
x_i + x_{i-1} + c_i ∈ {2, 5}
```
(because 2 ≡ 2 mod 3 and 5 ≡ 2 mod 3)

**Allowed sums**: {0, 1, 3, 4, 6}, corresponding to:
- (y_i, c_{i+1}) ∈ {(0,0), (1,0), (0,1), (1,1), (0,2)}

**State space**: (x_{i-1}, c_i) ∈ {0,1,2} × {0,1,2} = 9 states total

So "4X has only digits {0,1}" is a **finite-state constraint** on the sequence (x_i).

### Step 4: The Backward Chain Problem

Apply to X = 4^{m-1} and 4X = 4^m.

If 4^m has digits only {0,1}, then base-3 digits of X = 4^{m-1} must form an **input word** accepted by the "×4 outputs only 0/1" transducer.

Because 4^m being a power of 4 means you can divide by 4 repeatedly:
```
4^m → 4^{m-1} → 4^{m-2} → ⋯ → 4^0 = 1
```

Any solution m gives a **finite backward chain** of accepted inputs, ending at 1.

### Step 5: The "Power of 2" Choke Point

The carry automaton describes all X such that 4X lands in the Cantor digit set. There are many such X (survivor count doubles each level).

**The decisive extra input**: X = 4^{m-1} is a **pure power of 2** (no odd prime factors).

In base-3, "X is a power of 2" is global and non-local. The aim:
- Extract from the carry automaton a finite list of digit-pattern consequences
- Show they force divisibility by 3 or some odd number
- Unless you're on a very specific rigid pattern

---

## The Key Sub-Lemma

> **Key sub-lemma (no eventually-0 exponent tail except trivial):**
>
> Consider the inverse-limit survivor set E ⊂ ℤ₃ of exponents m such that 4^m has no digit 2 in its 3-adic expansion.
>
> Then the only elements of E whose base-3 expansion is **eventually all zeros** (i.e., ordinary nonnegative integers) are m ∈ {0, 1, 4}.

**Translation**: The only integer exponents with infinite "always-take-the-0-child once modulus is large enough" tail are {0, 1, 4}, hence n ∈ {0, 2, 8}.

**In carry-transducer language**: Show that in the transducer for "X ↦ 4X lands in {0,1}-digits", the only paths that can be extended by reading infinitely many input 0's without forcing output digit 2 are exactly those for X = 4^t with t ∈ {0, 1, 4}.

This becomes a **finite graph problem** once you incorporate "power-of-2" as state invariants.

---

## Three Sufficient Properties

### (1) Uniform Eventual j=0 Death

Prove: For every integer n > 8, there exists k ≤ C log n such that the k-th ternary digit of 2^n is 2.

This gives explicit kill depth for each n → nontrivial min diverges.

### (2) Bounded-Ones Reduction

**Dimitrov-Howe (via Saye)**: If 2^n has no ternary digit 2 and has ≤ 25 ternary 1's, then n ∈ {0, 2, 8}.

So it suffices to prove the **purely combinatorial** statement:

> Any power 2^n whose ternary digits are all {0, 1} has at most 25 ones.

This is a concrete "bridge lemma" to aim at.

### (3) Automaton Cycle Exclusion

Build a finite automaton generating exactly the admissible inverse-limit E ⊂ ℤ₃ (Abram-Lagarias style constructions). Then prove:

> The only accepting state with an outgoing edge labeled "0" to itself (a 0-loop) reachable from the start corresponds to m ∈ {0, 1, 4}.

This is exactly the "no eventually-zero expansions beyond trivial" claim.

---

## Proof Strategy Summary

1. **Build the 9-state directed graph** of allowed transitions:
   ```
   (x_{i-1}, c_i) --[x_i]--> (x_i, c_{i+1})
   ```
   with constraint y_i ∈ {0, 1}

2. **Prove structural lemmas** about strongly connected components:
   - Any component permitting arbitrarily long words forces either X ≡ 0 (mod 3) or X ≡ 0 (mod 6)
   - Or has unique "carry-control tail" occurring only finitely often along chain, producing exactly 256

3. **Conclude** only m = 0, 1, 4 survive full back-division by 4

---

## References

1. Saye (2022): [JIS Paper](https://cs.uwaterloo.ca/journals/JIS/VOL25/Saye/saye3.pdf)
2. Abram-Lagarias (2013): [arXiv:1308.3133](https://arxiv.org/abs/1308.3133)
