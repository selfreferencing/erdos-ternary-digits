# Master Synthesis: GPT Exploration of Erdős Ternary Digits Conjecture

**Date:** January 30, 2026
**Purpose:** Consolidate findings from 8 GPT responses on the "log-time cancellation" problem

> **NOTE**: This document covers GPT Responses 1-8. For the complete synthesis including all 11 GPT responses and 4 Gemini reports, see **FINAL_SYNTHESIS_ALL_RESPONSES.md**

---

## The Conjecture

**Erdős (1979)**: The only n ≥ 0 such that 2^n contains no digit 2 in base 3 are n = 0, 2, 8.

- 2^0 = 1 = (1)₃
- 2^2 = 4 = (11)₃
- 2^8 = 256 = (100111)₃

**Status**: Open. Verified computationally to n ≈ 6×10²¹ (Saye 2022).

---

## Key Insight 1: Correct Mathematical Formulation

**CRITICAL CORRECTION (Response 3)**: The problem is NOT about the rotation {n·log₃2 mod 1}.

### Wrong Formulation
- Rotation on [0,1) hitting the middle-third Cantor set
- This only captures leading-digit / Benford-type phenomena

### Correct Formulation (Lagarias)
Let Σ_{3,2̄} ⊂ Z₃ be the 3-adic Cantor set (digits in {0,1}).

Then:
```
2^n has no digit 2 in base 3  ⟺  2^n ∈ Σ_{3,2̄} ⊂ Z₃
```

Equivalently: the orbit of 1 under T(x) = 2x in Z₃ hits Σ_{3,2̄} only at n = 0, 2, 8.

---

## Key Insight 2: The 2D Landscape

**Response 6** places the problem in a 2×2 classification:

```
                     TARGET AXIS
          Fourier-decay              Resonant
          (Rajchman, Salem)          (Lattice, digit-defined)
                │                         │
  ──────────────┼─────────────────────────┼────────────────
                │                         │
  Mixing /      │    QUADRANT A           │    QUADRANT B
  Spectral Gap  │    (Most solved)        │    (Often tractable)
                │                         │
  D ────────────┼─────────────────────────┼────────────────
  Y             │                         │
  N             │    QUADRANT C           │    QUADRANT D
  A             │    (Best-understood     │    ★ YOUR PROBLEM ★
  M             │     non-mixing)         │    Methods thin out
  I             │                         │
  C             │                         │
  S             │                         │
                │                         │
  Pure Rotation │                         │
```

**Erdős lives in QUADRANT D**: Pure rotation (no mixing) + Resonant target (lattice structure).

This is the hardest quadrant because:
1. Rotations have pure point spectrum → no correlation decay
2. Ternary Cantor is maximally resonant → no Fourier decay
3. Any BC mechanism must come from number theory, not dynamics

### The Critical Third Axis (Response 8)

**Quantifier axis**: "for μ-a.e. starting point / a.e. parameter" vs "for this specific starting point and this specific parameter."

- Almost all clean BC/strong BC literature lives in the **a.e.** world
- Erdős is in the **single exceptional orbit** world
- This is why generic tools don't apply

### Boundary Theorem in Quadrant C (Response 8)

**Kurzweil's Theorem**: The monotone shrinking target property (MSTP) for circle rotations holds **iff** the rotation angle is **badly approximable**.

This is a genuine boundary—but it's **arithmetic**, not Fourier. There is NO clean "Fourier decay exponent > X → finite hits" theorem.

---

## Key Insight 3: Why Standard Tools Fail

### Discrepancy Theory (Response 2A)
- Even perfect discrepancy gives #{n ≤ N : hit} = o(N)
- Still allows infinitely many hits
- Need UNIFORM bound #{n ≤ N : hit} ≤ C for all N

### Shrinking Targets (Response 7)
- Standard STP designed for single-interval targets
- Erdős target has 9^d components at depth d
- Koksma bounds blow up: Var(1_{S_d}) ~ 9^d destroys approach

### ×2×3 Rigidity (Response 2B)
- Powerful for measures and entropy
- Gives dimension bounds (dim ≤ log₃φ ≈ 0.438)
- Does NOT constrain specific orbits
- Exceptional sets not known to be closed

### Fourier/Structured Sets (Response 2A, 8)
- Cantor self-similarity creates resonances at powers of 3
- Cantor measures are NOT Salem (no polynomial Fourier decay)
- Standard structured-set discrepancy is blocked
- **Critical (Response 8)**: The classic Cantor measure's Fourier transform **doesn't even tend to 0 at infinity**—it has NO Fourier decay at all. This is the extreme "resonant" end.

---

## Key Insight 4: The Critical Negative Result

**There CANNOT be a general "log-time cancellation" theorem** (Response 2A):

> If α ∈ C₃ (the Cantor set) is irrational, then {3^k α} ∈ C₃ for all k ≥ 0.

This means:
- Uncountably many irrational α (dimension log₃2) hit C₃ infinitely often
- Any theorem would need strong hypotheses excluding this family
- The "specific-α" version (λ = 1) requires arithmetic input

---

## Key Insight 5: Current State of Knowledge

| Result | Source |
|--------|--------|
| Verified to n ≤ 2·3^45 ≈ 6×10²¹ | Saye 2022 |
| Counting bound N(X) ≪ X^{log₃2} | Lagarias/Narkiewicz |
| dim(E(Z₃)) ≤ log₃φ ≈ 0.438 | Abram-Bolshakov-Lagarias 2015 |
| ≤25 ones → only n=0,2,8 | Dimitrov-Howe |
| Conjecture still open | Ren-Roettger 2025 |

**Note**: The dimension bound was already improved from 1/2 to ~0.438. Still far from finiteness.

---

## Key Insight 6: The Minimal Lemma

**Response 5** identifies what would actually suffice:

Since (1, 4, 256) are already hits, conjecture equivalent to "no fourth hit."

### Formulation A: 4-Fold Intersection Emptiness
> For every m > 8: C(1, 4, 256, 2^m) ∩ Z₃× = ∅

(No 3-adic UNIT can simultaneously satisfy digit-2 omission at exponents 0, 2, 8, m)

### Formulation B: Carry-Forces-Divisibility
> If a 3-adic unit λ has λ, 4λ, 256λ, 2^m λ all omitting digit 2 for some m > 8, then λ ≡ 0 (mod 3), contradiction.

**One-line target**: "Four constraints force a factor of 3."

---

## Key Insight 7: The Research Program

**Response 4 & 5** outline a 5-step program:

### Step 1 (Most Tractable): Build Automaton Infrastructure
- Implement automaton construction for C(M₁, ..., M_k)
- Look for structural invariants ("no unit paths", etc.)

### Step 2: Prove Unit-Exclusion Criterion
- Theorem: If M₁, ..., M₄ have certain ternary/carry property, then C(...) ⊆ 3Z₃
- Specialize to (1, 4, 256, 2^m)

### Step 3: Push Metric Side
- Improve dim(E) beyond log₃φ, or prove dim = 0

### Step 4: Hybrid Sieve
- Dimitrov-Howe style without fixed bound on # of 1s
- Derive necessary conditions on digit string features

### Step 5 (Hardest): Conditional Bridge from Rigidity
- Prove: If [×2×3 rigidity] holds, then Erdős holds

---

## The Bottleneck (One Sentence)

> "All available tools either control a bounded amount of digit information OR give dimension/measure information about parameter sets, but Erdős demands a global, multi-scale 'no digit 2 anywhere' exclusion for a fixed orbit."

---

## Three Missing Pieces (Any One Would Suffice)

### 1. Multi-Scale Independence Theorem
- Prove digit positions of 2^n in base 3 are "independent enough" for Borel-Cantelli
- Obstruction: rotations aren't mixing, Cantor target is resonant

### 2. Uniform Intersection Bound
- Prove {n : 2^n has only 0,1 digits up to 3^k} is sparse enough
- Needs sum-product or exponential sum input with carries

### 3. Orbit-Level Rigidity Theorem
- Prove any λ whose ×2 orbit hits Cantor infinitely often lies in describable set
- Then show λ = 1 is not in that set

---

## Most Promising Path

**Carry dynamics / finite automata** (Response 4):

Uses special arithmetic of 2 and 3, not generic equidistribution.

Evidence this is fertile:
- Dimitrov-Howe "≤25 ones" is exactly this flavor
- Saye's recursion on trailing digits shows rich explicit structure
- Recursion tree might be provable to have no infinite branch

### Community's Implicit Judgment (Response 8)

The best results do NOT look like "cancellation estimates for fixed orbit." They look like "encode digit constraint by automata; bound Hausdorff dimension / nesting constants."

The community has implicitly judged that "Quadrant A methods" aren't the right tool and has built a different framework (3-adic dynamics + symbolic dynamics) where partial progress is possible.

---

## Four "Moves" Into Solvable Quadrants (Response 8)

| Move | Description | Caveat |
|------|-------------|--------|
| **1. Upgrade dynamics** | Add correlation decay (expanding/hyperbolic) | ×2 on Z₃ is isometry, no decay "for free" |
| **2. Soften target** | Work with k-th stage approximation | Proves neighborhood hitting, not exact |
| **3. Soften quantifier** | Average over α or λ | Different question (a.e. vs specific) |
| **4. Change target class** | Salem/random Cantor with Fourier decay | Different target entirely |

None of these moves preserve the exact Erdős problem, but each illuminates what makes it hard.

---

## Timeline Assessment

- **Open since**: late 1970s
- **Best unconditional**: zero density / fractal dim < 1, not finiteness
- **Assessment**: High-difficulty, potentially needing new rigidity idea
- **Horizon**: Multi-decade (50-year class, not 5-year)

**But**: Problems like this sometimes fall to unexpectedly "elementary" argument once right invariant is found.

---

## Key References

### Core Papers
- **Lagarias**: arXiv:math/0512006 — 3-adic framework, dim ≤ 1/2
- **Abram-Bolshakov-Lagarias**: arXiv:1508.05967 — Improved to log₃φ ≈ 0.438
- **Dimitrov-Howe**: arXiv:2105.06440 — "≤25 ones" gives only n=0,2,8
- **Saye**: JIS 2022 — Verification to 6×10²¹, trailing-digit recursion

### Shrinking Targets
- **Fayad**: arXiv:math/0501205 — MSTP for translations
- **Kim**: Shrinking target papers
- **Chaika-Constantine**: Quantitative results

### ×2×3 Rigidity
- **Shmerkin (2019)**: Annals — Intersection dimension
- **Rudolph/Einsiedler-Katok-Lindenstrauss**: Measure rigidity

### Recent
- **Ren-Roettger (2025)**: arXiv:2511.03861 — Digit frequency computations

---

## Next Steps for User

1. **If pursuing proof**: Attack Step 2 (unit-exclusion) via carry-automaton analysis
2. **If pursuing research program**: Start with Step 1 (build automaton infrastructure)
3. **If pursuing publication**: Subproblem 1 (push "few 1's" boundary) is most tractable

The Fourier route sketch offered by GPT could provide the conceptual pivot needed if the carry/automaton approach stalls.

---

## Verdict

This is a "needs new mathematics" problem, not an "apply existing tools more cleverly" problem. But the research program is coherent:

1. The minimal lemma is clearly stated (unit-exclusion)
2. The machinery exists (automata, dimension bounds)
3. Intermediate results are publishable
4. The 50-year timeline is realistic

The gap: **no mechanism to turn "small exceptional set" into "specific point excluded."**
