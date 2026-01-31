# GPT Response 11: Proof Template Analysis

**Date:** January 31, 2026
**Prompt:** PROMPT_LEVEL_B_2_PROOF_TEMPLATES.txt
**Type:** Structural Analysis

---

## Executive Summary

Five proof templates analyzed. **Most promising**: Hybrid of (4) Congruence-Lifting + (5B) Carry-Automaton. This aligns with both Dimitrov-Howe's success and Lagarias's dynamical framework.

---

## Template 1: Subspace Theorem / S-unit

### What It Proves

For **fixed k**, equations 2^n = Σ 3^{a_j} (k terms) have finitely many solutions.

**Dimitrov-Howe**: k ≤ 25 ⇒ n ∈ {0, 2, 8}

### Proof Skeleton

1. Encode "few 1's" as fixed-length S-unit relation
2. Apply Subspace Theorem ⇒ finitely many non-degenerate solutions
3. Make effective via arithmetic pruning

### Input Required

- **Fixed** number of terms k
- Multiplicative structure (S-units) + linear relation

### Why It Fails for Erdős

- Erdős allows **unbounded k**
- Finiteness is dimension-fixed: "for each k, finite" ≠ "uniformly finite"
- Bounds worsen rapidly with k

### What Would Make It Work

**Bridge lemma**: Prove any solution has k ≤ K for absolute constant K.

Options:
- Uniform sparsity bound
- Gap principle / compression to bounded terms
- Quantitative contradiction forcing k bounded

---

## Template 2: Transcendence / Linear Forms in Logarithms

### What It Proves

Effective finiteness for equations forcing |n log 2 - m log 3| to be very small.

### Proof Skeleton

1. Rewrite equation as near-multiplicative dependence
2. Apply Baker's theorem for lower bound
3. Finish with LLL / continued fractions

### Input Required

Equation forcing **excellent** rational approximations to log₃2.

### Why It Fails for Erdős

The digit-sum equation 2^n = Σ 3^{a_j} does NOT force 2^n ≈ 3^m.

In extremal case (all digits 1), ratio 2^n/3^m ≈ 3/2, not (1 + ε).

The linear form in logs is O(1), not exp(-Cm). Baker can't bite.

### What Would Make It Work

Force **tiny errors** from digit condition:
- Recursive remainder forcing tiny gaps
- Block-structure lemma creating exceptionally good approximations

---

## Template 3: Measure Rigidity (×2, ×3)

### What It Proves

Under positive entropy: joint ×2, ×3 invariant measures must be Haar.

### Proof Skeleton

1. Assume many structured exceptions
2. Upgrade combinatorial structure → entropy
3. Invoke measure classification (positive entropy ⇒ Haar)
4. Contradict "exceptional set is fractal"

### Input Required

- Create ×2, ×3 invariant measure from exceptions
- **Positive entropy hypothesis**

### Why It Fails for Erdős

Erdős exceptional set is:
- 3-adic Cantor-type set ∩ orbit {2^n}
- Supports **zero-entropy** measures
- Hard case of Furstenberg is exactly zero-entropy regime

### What Would Make It Work

- **Zero-entropy rigidity breakthrough**
- Adelic/homogeneous embedding bypassing entropy
- Prove infinitely many hits ⇒ positive entropy joining

---

## Template 4: Combinatorial / Congruence-Lifting

### What It Proves

Explicit classification for **bounded** number of 1's.

**Dimitrov-Howe**: ≤25 ones ⇒ n ∈ {0, 2, 8}

### Proof Skeleton

1. Work mod small M₁
2. Enumerate representations consistent with constraint
3. Lift to larger M₂, keep only liftable classes
4. Iterate until only global solutions remain
5. Verify surviving candidates

### Input Required

- Digit/sum constraint as finite congruence condition
- Good moduli where orders of 2, 3 are manageable

### Why It Fails for Erdős

- Unbounded k ⇒ combinatorial explosion
- No a priori cutoff on summands

### What Would Make It Work

- **Covering-congruence strategy**: Cover all n > 8 by classes forcing digit 2
- **Carry-propagation invariant**: Prove avoiding digit 2 forces rigid carry behavior
- **Multi-scale pruning**: Coarse + fine moduli building finite elimination tree

---

## Template 5: Automata-Theoretic

### 5A: Cobham-Style (Automatic ⇒ Periodicity)

If set is k-automatic AND ℓ-automatic (independent bases) ⇒ ultimately periodic.

**Why it doesn't solve Erdős**: Non-automatic ≠ finitely many 1's.

### 5B: Path-Set Emptiness / Inverse-Limit Automata

**This is the closest to structural proof.**

### Proof Skeleton

1. For each k, define N_k = {n : first k digits of 2^n avoid 2}
2. N_k is periodic mod φ(3^k) = 2·3^{k-1} ⇒ finite automaton
3. Full set N_∞ = ∩ N_k = inverse limit
4. Prove inverse-limit path set is finite (exactly {0, 2, 8})

### Input Required

- Clean automaton model of digit constraints under doubling
- Analysis of **inverse limit**, not just fixed k

### Why It Fails Now

- Each fixed k tractable, but controlling inverse limit uniformly is hard
- Current theory yields "dimension small" not "empty"

### What Would Make It Work

- **No-new-cycles theorem**: Once depth reached, every state forces digit 2
- **Carry-dynamics classification**: Only patterns producing {1, 4, 256} survive
- **Computer-assisted proof** with certified pruning invariant

---

## Synthesis: Most Likely to Succeed

**Hybrid of (4) + (5B): Carry-Automaton / Congruence-Lifting**

### Why This Looks Most Promising

1. Aligns with Dimitrov-Howe success (massive congruence pruning)
2. Aligns with Lagarias/Abram 3-adic dynamical / path-set framing
3. **Unbounded digit count not fatal** - constraint lives in finite state space (carries)

### Structure of Successful Proof

1. **Build doubling-in-base-3 transducer** (states = carry configurations)
2. **Impose forbidden output digit 2**, compute subgraph producing only {0,1}
3. **Prove rigidity lemma**: Every infinite path eventually periodic, every cycle = known solution
4. **Conclude**: Beyond cycles, every path dies (forces digit 2) ⇒ finitely many n

---

## Template Comparison Table

| Template | Works For | Fails Because | Missing Ingredient |
|----------|-----------|---------------|-------------------|
| Subspace/S-unit | Fixed k | k unbounded | Bridge lemma: k ≤ K |
| Baker/Transcendence | Near-equalities | No tiny errors | Block-structure forcing approximation |
| Measure Rigidity | Positive entropy | Zero entropy | Zero-entropy breakthrough |
| Congruence-Lifting | Bounded k | Combinatorial explosion | Covering or carry invariant |
| Automata (5B) | Finite state | Inverse limit hard | No-new-cycles theorem |

---

## The "Endgame Structure"

A plausible successful proof:

1. Model base-3 doubling as finite-state transducer (carry states)
2. Characterize states compatible with digits {0,1} indefinitely
3. Prove: Every infinite path becomes periodic (finite-state ⇒ eventual cycle)
4. Prove: Every admissible cycle corresponds to known solutions
5. Conclude: Beyond those cycles, every path forces digit 2

**This is the closest to a realistic proof structure.**

---

## Key References by Template

| Template | Key Paper |
|----------|-----------|
| S-unit | Dimitrov-Howe arXiv:2105.06440 |
| Baker | Standard (Evertse-Schlickewei-Schmidt) |
| Rigidity | Rudolph; survey arXiv:2110.05989 |
| Congruence | Dimitrov-Howe arXiv:2105.06440 |
| Automata | Lagarias arXiv:math/0512006, Abram-Lagarias EMS |
