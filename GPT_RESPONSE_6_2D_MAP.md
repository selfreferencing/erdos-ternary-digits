# GPT Response 6: The 2D Landscape Map

**Date:** January 30, 2026
**Prompt:** 2D map of dynamics vs target structure

---

## Two Quantifier Regimes

| Regime | Scope | Tools |
|--------|-------|-------|
| **BC / Metric** | μ-a.e. initial point, a.e. α | Borel-Cantelli, discrepancy |
| **Arithmetic / Fixed-Orbit** | Specific orbit point, specific α | **Dramatically harder** |

Your "log-time cancellation" lives in the arithmetic/fixed-orbit regime.

---

## The 2×2 Landscape

```
                         TARGET AXIS
              Fourier-decay              Resonant
              (Rajchman, Salem)          (Lattice, digit-defined)
                    │                         │
    ────────────────┼─────────────────────────┼────────────────
                    │                         │
    Mixing /        │    QUADRANT A           │    QUADRANT B
    Spectral Gap    │    (Most solved)        │    (Often tractable,
                    │    DBC, transfer op     │     but clustering)
    D               │    Poisson laws         │
    Y               │                         │
    N   ────────────┼─────────────────────────┼────────────────
    A               │                         │
    M               │    QUADRANT C           │    QUADRANT D
    I               │    (Best-understood     │    (YOUR PROBLEM)
    C               │     non-mixing)         │    Methods thin out
    S               │    Threshold is         │    dim ≤ log₃φ ≈ 0.438
                    │    Diophantine          │
    Pure Rotation   │                         │
                    │                         │
```

---

## Quadrant A: Mixing + Fourier-Decay

**Status**: Most solved quadrant.

**What's known**:
- Dynamical Borel-Cantelli for hyperbolic/Markov systems
- Strong BC / Poisson laws / EVL for shrinking sets
- Spectral gap → decay of correlations

**Proof templates**:
- Transfer operator → correlation decay
- Second-moment / cumulant → BC + strong laws
- Extreme value theory → Poisson/EVL

**Moral**: Mixing provides the cancellation you're missing; Fourier decay makes it even easier.

---

## Quadrant B: Mixing + Resonant

**Status**: Often still tractable, but subtle.

**What's known**:
- Can still get sharp rare-event behavior
- But may see **clustering** (visits in bursts) rather than Poisson
- Extremal Index tied to box dimension of intersections

**Key paper**: "Rare events for Cantor target sets" (arXiv:1903.07200)

**Caution**: Even strong mixing doesn't guarantee strongest STP for all sequences. Fayad constructs mixing examples where MSTP fails.

**Moral**: Mixing helps a lot, but resonant targets can force non-Poisson structure.

---

## Quadrant C: Pure Rotation + Fourier-Decay

**Status**: Best-understood non-mixing corner.

**What's known**:
1. Full STP is too strong — translations don't have it
2. **MSTP ⟺ badly approximable α** (Fayad's characterization)
3. Quantitative/strong BC for Khinchin-type sequences (Chaika-Constantine)
4. Refined STP conditions (Kim)

**Proof templates**:
- Continued fractions, Ostrowski expansions
- Denjoy-Koksma inequalities (BV observables)
- Metric inhomogeneous Diophantine approximation

**Key insight**: Threshold is **Diophantine**, not Fourier. Fourier decay doesn't magically create mixing.

---

## Quadrant D: Pure Rotation + Resonant (YOUR QUADRANT)

**Status**: Where current methods thin out.

### What's known (closest results)

| Result | Source |
|--------|--------|
| 3-adic exceptional set dimension ≤ 1/2 | Lagarias 2009 |
| **Improved to dim ≤ log₃φ ≈ 0.438** | Abram-Bolshakov-Lagarias 2015 |
| Conjecture: dim = 0 | Open |
| Erdős still open | Saye 2022, Ren-Roettger 2025 |

**Answer to "is 1/2 the frontier?"**: NO — already pushed to ~0.438, still far from finiteness.

### Why this quadrant is hard

1. **Rotations have pure point spectrum** — no correlation decay
2. **Middle-third Cantor is maximally resonant** — Fourier transform doesn't decay due to ×3 structure
3. Any BC mechanism must come from **number theory**, not dynamics

### "Any specific α" theorems?

For digit-restriction/Cantor targets and specific irrational α: **NO general theorems** of form "for this α, hits are finite" beyond:
- Reduction to known Diophantine inequalities (usually balls/intervals)
- p-adic/automata computations (don't resolve λ=1)

---

## Question 3: Is There a "Boundary Theorem" in Fourier Decay?

### For rotations + geometric targets (balls/intervals): YES

The boundary is **Diophantine**, not Fourier:
- MSTP ⟺ constant type / badly approximable
- Refined versions depend on shrinking rate + Diophantine exponents

### For "Fourier decay > X → finite hits for rotations": UNLIKELY

Why:
- Rotations don't mix
- Can plant countably many orbit points into a set without changing Fourier dimension
- Such threshold can only work in **metric/randomized regime**

### What boundary DOES exist (lattice vs non-lattice)

**Polynomial Fourier decay** is possible for:
- Nonlinear / nonlattice fractal measures
- Example: Gibbs measures for Gauss map with dim > 1/2 (Jordan-Sahlsten)

**What ternary Cantor is missing**: It's **arithmetically lattice** (×3 invariant), so maximally far from Fourier-decaying.

---

## Question 4: What Moves Problem Into Solvable Quadrant?

### (i) Upgrade dynamics to spectral gap

Re-encode as visits under expanding/hyperbolic map. Brings in transfer-operator methods.

### (ii) Keep rotation, change target to "regular" or smoothed

Convolve Cantor with smooth bump at scale 3^{-k}. Destroys sharp digit constraints but Fourier tractable.

Won't prove "no exact digit 2" but can prove "rare near-misses."

### (iii) Replace lattice Cantor with nonlattice

IFS with non-commensurable scales may support Rajchman measures with polynomial decay.

### (iv) Work in metric regime

Average over α or over Cantor measure. Powerful (ubiquity/mass-transference) but different quantifiers.

---

## Current Boundary of Knowledge (Your Quadrant)

| Aspect | Status |
|--------|--------|
| Best structural control | p-adic/automata → dim(E) ≤ log₃φ ≈ 0.438 |
| What's missing | Mechanism: "exceptional set small" → "λ=1 not exceptional" |
| Empirical | Massive computation (10²¹), no proof |

---

## Reading Path by Quadrant

### 1. Rotations + Shrinking Targets (easier targets)
- Fayad: arXiv:math/0501205 (MSTP ⟺ constant type)
- Kim: shrinking target papers
- Chaika-Constantine: quantitative results

### 2. Mixing + Cantor Targets (easier dynamics)
- "Rare events for Cantor target sets": arXiv:1903.07200

### 3. Your Exact Quadrant
- Lagarias: arXiv:math/0512006
- Abram-Lagarias 2014 (EMS)
- Abram-Bolshakov-Lagarias 2015: arXiv:1508.05967

### 4. Targets with Fourier Decay
- Jordan-Sahlsten: arXiv:1312.3619
- Sahlsten-Stevens survey

---

## Key New References

| Paper | Topic |
|-------|-------|
| arXiv:1903.07200 | Rare events for Cantor target sets |
| arXiv:math/0501205 | Fayad: MSTP for translations |
| arXiv:1312.3619 | Jordan-Sahlsten: Fourier decay Gauss map |
| Chaika-Constantine | Quantitative shrinking targets |
| Kim (Dongguk) | STP for irrational rotations |

---

## Bottom Line

Your problem (Quadrant D) is hard because:
1. Pure rotation = no mixing = no correlation decay
2. Ternary Cantor = lattice = no Fourier decay
3. Best known: dim ≤ 0.438, far from "λ=1 not exceptional"

The gap: **no mechanism to turn "small exceptional set" into "specific point excluded."**
