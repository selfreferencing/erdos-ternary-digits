# GPT Response 4: Research Program Synthesis

**Date:** January 30, 2026
**Prompt:** Integration prompt — research program design

---

## Current State of Knowledge (Jan 2026)

### What's Known

| Result | Source |
|--------|--------|
| Verified to n ≤ 2·3^45 ≈ 6×10²¹ | Saye (2022) |
| If no digit 2, must have ≥26 ones | Dimitrov-Howe (arXiv:2105.06440) |
| dim(E(Z_3)) ≤ log₃φ ≈ 0.438 | Abram-Bolshakov-Lagarias |
| Even limiting frequency unknown | Ren-Roettger (2025) |

### The Core Bottleneck (Lagarias)

Both real method (leading digits) and 3-adic method (trailing digits) only control ~log₃X digits among ~n total digits. Each method alone reduces candidates to ≪ X^c (c < 1), but **combining the two kinds of information in a quantifiable "uncorrelation" way** is explicitly highlighted as the missing ingredient.

---

## Answer 1: Is "Log-Time Cancellation" the Right Framing?

**It's the right diagnosis, but probably not the right target theorem.**

Why:
- Any theorem like "for k digits, orbit gives cancellation at scale k" is a digit-normality / strong pseudorandomness statement
- That's in the same difficulty class as proving base-3 normality of explicit constants (basically impossible)

**Better framing**: Something more structural/rigid that uses:
- Special arithmetic of bases 2 and 3
- Carry dynamics of ×2 in base 3
- Automaton/path-set structure specific to powers of 2

---

## Answer 2: The Minimal New Result

Two plausible "minimal lemma" choices:

### (A) Bounded-Hamming-Weight Lemma (Dimitrov-Howe direction)

> Prove: If 2^n has ternary digits only 0/1, then it has at most B ones.

Combine with Dimitrov-Howe (already proved: no examples with ≤25 ones except n=0,2,8).

If B ≤ 25, conjecture is finished in one shot.

### (B) Carry/Automaton Rigidity Lemma (3-adic/path-set direction)

> Any orbit segment under ×2 that stays inside Σ_{3,2̄} for more than L steps must lie in one of finitely many explicitly classifiable "templates," and those templates do not include the orbit of 1 beyond the known cases.

This is a finite-type exclusion statement, attackable via Abram-Bolshakov-Lagarias machinery.

### What NOT to pick

- "Show dim(E) = 0" — not sufficient (countable/finite is much harder)
- "Log-time discrepancy" — as hard as normality
- "Theorem for badly approximable α" — doesn't match 3-adic structure

**Recommended**: Option (B) — carry/automaton rigidity specialized to starting point 1.

---

## Answer 3: Most Likely Path to Success (Ranked)

### 1. MOST PLAUSIBLE: Carry dynamics / finite automata

Uses special arithmetic of 2 and 3, not generic equidistribution.

Evidence this is fertile:
- Dimitrov-Howe "≤25 ones" is exactly this flavor
- Saye's recursion on trailing digits shows rich explicit structure
- Recursion tree might be provable to have no infinite branch

### 2. Quantify independence between leading/trailing digits

Exactly what Lagarias flags as missing. Even tiny exponent improvement (replacing log₃2 by something smaller) is publishable.

### 3. Extend dimension arguments to show dim = 0

Major conceptual win, but Lagarias warns countable/finite is much harder.

Also: generalizing too much provably CAN'T drive dimension to 0.

### 4. LEAST PLAUSIBLE: Prove generic behavior of log₃2 (normality-type)

Likely true, computations support it, but mathematically out of reach. Ren-Roettger explicit: "beyond current technology."

---

## Answer 4: Timeline Assessment

- **5-year problem**: Unlikely
- **50-year / needs new math**: More realistic

**High-risk long-horizon problem**: Might fall to clever structural/carry argument that looks "elementary in retrospect," but no established pipeline makes that predictable.

---

## Answer 5: The 5-Subproblem Research Program

### Subproblem 1 (Most Tractable): Push "Few 1's" Boundary

**Starting point**: Dimitrov-Howe (≤25 ones)

**Goal**: Extend classification "no solutions with ≤B ones" from B=25 to larger B, or prove B(n) must grow with n.

**Method**: Congruence-sieving with carefully chosen moduli.

**Payoff**: Every increment in B is a real theorem; strengthens carry-rigidity intuition.

### Subproblem 2: Explicit Carry-Transducer Model

**Goal**: Encode ×2 on ternary digits as finite-state transducer (carry as state). Study induced graph on "allowed" {0,1} configurations.

**Concrete targets**:
- Classify all cycles / eventually periodic paths in constrained carry graph
- Prove starting from digit string for 1, no path of length >L stays within {0,1}-digits except known hits

**Why tractable**: Bounded-state symbolic dynamics; computation-guided conjectures then certification.

### Subproblem 3: Saye's Trailing-Digit Recursion → No Infinite Branches

**Goal**: Turn Saye's recursion into theorem:
```
∩_{k≥1} {n : last k ternary digits of 2^n lie in {0,1}} = {0, 2, 8}
```

**Why promising**: "Finite branching tree / no infinite path" statements sometimes yield to clever invariants (monotone measure of carry complexity, modulus-lifting obstruction).

### Subproblem 4: High/Low Digit Decorrelation

**Goal**: Improve upper bound on counting function N₁(X) = #{1≤n≤X : (2^n)₃ omits digit 2} from X^{log₃2} to X^β with β < log₃2.

**Why publishable**: Any exponent drop is meaningful progress; connects to broader themes in dynamical systems / digital expansions.

### Subproblem 5 (Hardest): Connect to Rigidity / Invariant Measures

**Goal**: Show if 2^n hits Σ_{3,2̄} infinitely often, can construct nontrivial invariant measure under some semigroup action, contradicting known rigidity.

**This is the "new mathematics" tier** — might be where conceptual breakthrough comes from.

---

## Should You Work on This?

### If goal is to SOLVE Erdős outright:
Very high-risk bet. Exact bottleneck is real. Experts characterize as "beyond current tools."

### If goal is PUBLISHABLE RESEARCH PROGRAM:
Yes — but pick waypoint-driven plan, not direct assault.

**Productive lines**:
- Congruence-sieving/Hamming-weight (Dimitrov-Howe style) — demonstrably productive
- Recursion/tree approach (Saye style) — explicit combinatorial object to prove finite
- Automaton/path-set (Abram-Bolshakov-Lagarias) — strong infrastructure, exact computables

---

## Three Toolkits Offered

GPT offers to sketch concrete first project for whichever you're most comfortable with:

| Toolkit | Style |
|---------|-------|
| **Symbolic dynamics / automata** | Carry transducer, path-set classification |
| **Congruences / sieve** | Extend Dimitrov-Howe bounds |
| **p-adic dynamics** | Exceptional set geometry, dimension bounds |

---

## Key References

### Core
- **Dimitrov-Howe**: arXiv:2105.06440 — "≤25 ones" theorem
- **Saye**: JIS 2022 — verification to 6×10²¹, trailing-digit recursion
- **Abram-Bolshakov-Lagarias**: arXiv:1508.05967 — improved dimension bound
- **Lagarias**: arXiv:math/0512006 — 3-adic framework, "two methods don't combine"

### Recent
- **Ren-Roettger (2025)**: arXiv:2511.03861 — digit frequency computations

### Framework
- **Lagarias Part II**: ResearchGate — nesting constant, dimension bounds
- **Lagarias slides**: U-M LSA — real/3-adic comparison, digit-reversal map

---

## Bottom Line

The problem is genuinely hard (50-year class), but there's a clear incremental research program:

1. Push Dimitrov-Howe boundary (most tractable)
2. Build carry-transducer model
3. Prove Saye recursion tree is finite
4. Quantify digit decorrelation
5. Connect to rigidity (hardest)

Each step is publishable even if the main conjecture remains open.
