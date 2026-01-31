# GPT Response 12: Five-Field Mapping

**Date:** January 31, 2026
**Prompt:** PROMPT_LEVEL_B_1_FIELD_MAPPING.txt
**Type:** Field-by-Field Analysis

---

## Executive Summary

Five mathematical fields analyzed for relevance to Erdős. **Most promising**: Fractal geometry / Hausdorff dimension (realized through p-adic symbolic dynamics and automata) because it has produced problem-specific structure (automata models, exact dimension formulas, best bounds).

---

## Current State Summary

| Result | Source |
|--------|--------|
| Computational verification | n ≤ 2·3^45 ≈ 5.9×10²¹ | Saye (2022) |
| Bounded Hamming weight | ≤25 ones ⇒ n ∈ {0,2,8} | Dimitrov-Howe |
| 3-adic exceptional set dim | ≤ log₃φ ≈ 0.438 | Abram-Bolshakov-Lagarias |
| Digit frequency evidence | Uniform up to n = 10⁶ | Ren-Roettger (2025) |

**Central paper**: Lagarias's *Ternary expansions of powers of 2* - two dynamical models (real and 3-adic), exceptional set conjectures, obstacle: leading-digit and trailing-digit approaches hard to combine.

---

## Field 1: Ergodic Theory / Dynamical Systems

### Why Relevant

The orbit {nα mod 1} with α = log₃(2) is an irrational circle rotation. Digit-avoidance events encode as hitting a fractal target finitely often.

### Key Papers/Authors

- **Jimmy Tseng** (2007/2008): "On circle rotations and the shrinking target properties" - necessary/sufficient conditions for generalized shrinking-target property
- **Jaroslav Kurzweil** (1955): Early dynamical Borel-Cantelli for rotations
- **Chaika-Constantine**: Shrinking targets in interval exchanges

### Tools That Might Apply

- Borel-Cantelli philosophy for dynamical systems
- Continued fractions / Diophantine type → recurrence estimates
- Discrepancy bounds (Erdős-Turán), Denjoy-Koksma estimates

### Why Standard Techniques Fail

1. **Rotations are uniquely ergodic but not mixing** - many BC results need mixing/correlation decay
2. **Target is fractal, not a ball** - most theorems stated for balls B(x, rₙ)
3. **Need statement for specific α = log₃(2)**, not "almost every α"

### Open Problems That Would Imply Progress

- Shrinking-target theorem for fixed rotation by log₃(2) where targets are ternary cylinders
- Effective decorrelation estimate across scales for rotation relative to ternary digit partitions

---

## Field 2: Diophantine Approximation

### Why Relevant

Orbit behavior of nα mod 1 governed by how well α is approximated by rationals.

### Key Papers/Authors

- **Dimitrov-Howe**: Clean exemplar when number of nonzero digits bounded
- **Lagarias**: Frames problem as exponential Diophantine/dynamical hybrid

### Tools That Might Apply

- Linear forms in logarithms / transcendence bounds (Baker theory)
- S-unit equations / Subspace theorem
- Badly approximable numbers + Schmidt games
- Modular sieving and lifting (Dimitrov-Howe method)

### Why Standard Techniques Fail

1. **Variable-length S-unit problem**: Number of 1's not bounded a priori
2. **Transcendence bounds too weak** to force digit 2 to appear

### Open Problems That Would Imply Progress

- Prove log₃(2) has strong explicit Diophantine property
- New framework for S-unit equations with unbounded terms but restricted digits

---

## Field 3: Fractal Geometry / Hausdorff Dimension

### Why Relevant

Digit restrictions define self-similar sets. Exceptional sets naturally studied by Hausdorff dimension.

### Key Papers/Authors

- **Lagarias**: Formulates dimension conjectures in real and 3-adic models
- **Abram-Bolshakov-Lagarias**:
  - Intersection fractals describable by finite automata
  - Dimensions exactly computable as log₃(β) for algebraic β
  - Upper bound log₃(φ) ≈ 0.438 for 3-adic exceptional set

### Tools That Might Apply

- Intersection theory for self-similar/invariant sets
- Entropy/rigidity from ×2/×3 dynamics (Furstenberg theme)
- Symbolic dynamics + thermodynamic formalism
- Spectral radius methods (dimension = log of Perron eigenvalue)

### Why Standard Techniques Fail

1. **Dimension ≠ emptiness**: Even dim = 0 doesn't exclude specific point "1"
2. **Many theorems are generic** ("almost every"), Erdős pins down specific arithmetic scaling

### Open Problems That Would Imply Progress

- Strengthen from "dimension small" to rigidity/classification: "only points with infinitely many hits are explicit"
- Prove exceptional set countable or classify its symbolic structure

---

## Field 4: p-adic Analysis

### Why Relevant

Natural 3-adic formulation: orbit of point under ×2 meeting 3-adic Cantor set.

### Key Papers/Authors

- **Lagarias**: 3-adic model and exceptional set conjecture
- **Abram-Bolshakov-Lagarias**: Define Σ_{3,2̄} (digits 0,1), exceptional set E(Z₃), conjecture dim = 0
- **Saye**: Computational method is p-adic trailing-digit construction

### Tools That Might Apply

- p-adic dynamics on Z₃ (×2 as map on compact ring)
- Congruence-lifting / Hensel-type recursion
- p-adic fractal geometry

### Why Standard Techniques Fail

**Lagarias's meta-obstacle**:
- Real model sees leading digits (most significant)
- 3-adic model sees trailing digits (least significant)
- Each approach only reduces candidates to sublinear set ~X^{log₃2}
- "It seems challenging to combine the methods"

### Open Problems That Would Imply Progress

- Bridge theorem coupling 3-adic trailing constraints to leading digit constraints
- Sharper structural description of E(Z₃) beyond dimension bounds

---

## Field 5: Automata Theory / Symbolic Dynamics

### Why Relevant

Digit constraints are naturally symbolic. Intersection fractals representable by finite automata ("path-set fractals") with computable dimensions.

### Key Papers/Authors

- **Abram-Bolshakov-Lagarias**: Intersection sets' 3-adic expansions describable by labeled paths in finite automaton
- **Saye**: Recursion viewable as exploring digit-extension tree
- **Allouche-Shallit**: *Automatic Sequences* (standard reference)

### Cobham's Theorem (Why It Matters)

If a set is recognizable by finite automata in two multiplicatively independent bases, it must be ultimately periodic.

**Expectation setter**: Don't expect ternary expansions of {2^n} to have low-complexity automaton descriptions interacting nicely with both bases.

### Tools That Might Apply

- Finite automata / regular languages for constrained digit expansions
- Graph spectral radius methods
- Symbolic dynamics: subshifts of finite type

### Why Standard Techniques Fail

1. Encoding "is a power of 2" in base 3 with carry propagation - complexity explodes with length
2. Cobham rigidity suggests no clean uniform finite-automaton characterization spanning bases 2 and 3

### Open Problems That Would Imply Progress

- Finite-state obstruction: automaton describing "reachable as 2^n in base 3" AND "digits avoid 2" has only finitely many accepting paths
- Carry analysis theorem: long carry chains force digit 2 when multiplying by 2 repeatedly

---

## Verdict: Most Likely Field

**Fractal geometry / Hausdorff dimension** (realized through p-adic symbolic dynamics and automata)

### Why This Field

1. **Problem-specific structure already produced**: explicit automata models, exact dimension formulas, best bounds (log₃φ)

2. **Interfaces with ×2/×3 rigidity program** (Furstenberg-type phenomena) where deep entropy/rigidity tools developed

3. **Lagarias diagnosis**: Crux is multi-scale coupling of leading and trailing digits. Automaton/fractal viewpoint is cleanest language for "multi-scale digit structure"

### Caveat

Full resolution likely needs **bridge ingredient** drawing from at least two fields:
- Fractal/automaton structure + Diophantine input about log₃(2), OR
- New shrinking-target theorem for rotations against fractal targets

---

## Key References by Field

| Field | Key Paper |
|-------|-----------|
| Ergodic | Tseng arXiv:math/0702853 |
| Diophantine | Dimitrov-Howe arXiv:2105.06440 |
| Fractal | Abram-Bolshakov-Lagarias arXiv:1508.05967 |
| p-adic | Lagarias arXiv:math/0512006 |
| Automata | Allouche-Shallit (Cambridge) |
| Rigidity | Tal survey arXiv:2110.05989 |
