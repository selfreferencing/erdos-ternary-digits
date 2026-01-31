# GPT Responses 2A & 2B: Field Mapping and Negative Results

**Date:** January 30, 2026
**Prompts:** Level (b) meta-prompts on field identification and proof templates

---

## Key Findings

### The Problem Splits Into Two Versions

| Version | Statement | Difficulty | Status |
|---------|-----------|------------|--------|
| **Metric** | "For a.e. α, finitely many hits" | EASY | Follows from Borel-Cantelli (Σ k(2/3)^k < ∞) |
| **Specific** | "For α = log₃2 specifically" | HARD | Open, exactly where ×2/×3 machinery lives |

**The Erdős conjecture requires the specific-α version (λ = 1).**

---

## The Critical Negative Result

**There CANNOT be a general "log-time cancellation" theorem:**

> If α ∈ C₃ is irrational, then {3^k α} ∈ C₃ for all k ≥ 0.

This means uncountably many irrational α (Hausdorff dimension log₃2) have orbits that hit C₃ infinitely often. Any theorem would need strong hypotheses excluding this family.

---

## Why Each Approach Fails

### Discrepancy Theory
- Even perfect discrepancy gives #{n ≤ N : hit} = o(N)
- This still allows infinitely many hits
- Need UNIFORM bound #{n ≤ N : hit} ≤ C for all N
- This is beyond what discrepancy theory delivers

### Fourier/Structured Sets
- Cantor self-similarity creates resonances at powers of 3
- Cantor measures are NOT Salem (no polynomial Fourier decay)
- Standard "structured-set discrepancy" approach is blocked

### Shrinking Targets
- Standard shrinking targets: |nα - x| < r_n i.o.
- Erdős needs: nα ∈ F exactly (multi-scale simultaneous constraint)
- Much sharper than neighborhood hitting
- Rotation shrinking-target theory not designed for exact membership

### ×2×3 Rigidity
- Powerful for measures and entropy
- Gives dimension bounds for exceptional sets (Lagarias: dim ≤ 1/2)
- Does NOT constrain specific orbits
- Exceptional sets not known to be closed, so closed-set rigidity doesn't apply

---

## The Bottleneck (One Sentence)

> "All available tools either control a bounded amount of digit information OR give dimension/measure information about parameter sets, but Erdős demands a global, multi-scale 'no digit 2 anywhere' exclusion for a fixed orbit."

---

## The Three Missing Pieces

Any ONE would suffice, but none exist:

### 1. Multi-Scale Independence Theorem
- Prove digit positions of 2^n in base 3 are "independent enough" for Borel-Cantelli
- Obstruction: rotations aren't mixing, Cantor target is resonant
- Would be genuinely new/strong

### 2. Uniform Intersection Bound
- Prove {n : 2^n has only 0,1 digits up to 3^k} is sparse enough
- Needs sum-product or exponential sum input with carries
- Would look like deep arithmetic input

### 3. Orbit-Level Rigidity Theorem
- Prove any λ whose ×2 orbit hits Cantor infinitely often lies in describable set
- Then show λ = 1 is not in that set
- Obstruction: exceptional sets not known to be closed (Lagarias)

---

## The "Two Methods Don't Combine" Problem

From Lagarias's slides:

> "Both a real-model argument and a 3-adic-model argument separately cut the count of 'bad' times down to O(x^{log₃2})... yet **no one knows how to combine the information in the two methods**"

This is the exponential-gap issue stated as a known obstruction.

---

## The Exceptional Set Status

| Bound | Value | Source |
|-------|-------|--------|
| Known upper | dim ≤ 1/2 | Lagarias (2009) |
| Improved upper | dim ≤ log₃(φ) ≈ 0.438 | Abram-Bolshakov |
| Conjectured | dim = 0 | — |
| Known contents | **Unknown if anything beyond {0}** | EMS paper |

---

## Technical Correction

The actual fractal target for the orbit {nα} is:
```
F = log₃(1 + C₃) ⊂ [0,1)
```
not C₃ itself. But x ↦ log₃(1+x) is bi-Lipschitz on [0,1/2], so dim_H(F) = dim_H(C₃) = log₃2. All fractal questions remain essentially the same.

---

## Key References Identified

### Core Papers
- **Lagarias (2009)**: arXiv:math/0512006 — 3-adic framework, dim ≤ 1/2 bound
- **Abram-Bolshakov**: arXiv:1508.05967 — Improved bound log₃(φ) ≈ 0.438, automaton methods
- **Dimitrov-Howe**: arXiv:2105.06440 — "At most 25 ones" gives only n=0,2,8

### Shrinking Targets
- **Survey**: arXiv:2511.02377 — Dynamical Borel-Cantelli
- **Tseng**: AIMS paper — Shrinking targets for rotations

### ×2×3 Rigidity
- **Shmerkin (2019)**: Annals — Intersection dimension conjecture
- **Rudolph/Einsiedler-Katok-Lindenstrauss**: Measure rigidity

### Diophantine on Fractals
- **Allen-Chow-Yu**: Warwick paper — Dyadic approximation in Cantor set
- **Baker**: arXiv:2203.12477 — Metric results

### New (2026)
- **Gilson**: arXiv:2601.11799v2 — Quadratic irrationals via Thue-Mahler

### Computational
- **Saye (2022)**: JIS — Verified to n ≈ 6 × 10²¹

### Slides/Surveys
- **Lagarias slides**: math.lsa.umich.edu/~lagarias/talks-files/fields-horz6.pdf
- **Stoll slides**: CIRM — Lower bounds on nonzero digits

---

## People to Read/Contact

### Automata/3-adic
- William C. Abram
- Artem Bolshakov

### Shrinking Targets
- Stefano Galatolo
- Jyhshing Tseng

### Dyadic Approximation
- Demi Allen, Sam Chow, Han Yu
- Simon Baker

### Specific-Orbit Diophantine
- Frank Gilson (2026 preprint)

### ×2×3 Rigidity
- Pablo Shmerkin
- Michael Hochman

---

## The Three Directions

GPT asks which to pursue:

| Direction | Approach | Foothold |
|-----------|----------|----------|
| **(A) Fourier/exponential sums** | Push on resonance issue | Hardest — resonances block standard methods |
| **(B) p-adic dynamics + rigidity** | Extend Lagarias | Closest to existing infrastructure |
| **(C) Diophantine approximation** | Extend Dimitrov-Howe | Has partial result ("≤25 ones") |

---

## Verdict

The problem is genuinely hard. No existing framework comes close to solving it. Would require one of three "missing pieces" that don't currently exist. The specific-α version (which Erdős requires) is in the "arithmetic exceptional" world where methods are lacking.

The most honest assessment: this is a "needs new mathematics" problem, not a "apply existing tools more cleverly" problem.
