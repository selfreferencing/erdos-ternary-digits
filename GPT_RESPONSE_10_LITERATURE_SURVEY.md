# GPT Response 10: Comprehensive Literature Survey

**Date:** January 31, 2026
**Prompt:** PROMPT_LEVEL_A_1_LITERATURE_SEARCH.txt
**Type:** Annotated Bibliography

---

## Status Note

As of January 31, 2026, the conjecture is still treated as **open** in mainstream/peer-reviewed literature.

---

## Quick Reference: Best Known Bounds

Let α₀ = log₃2 ≈ 0.631.

| Bound Type | Value | Source |
|------------|-------|--------|
| Sparsity of solutions | N₁(X) ≪ X^{α₀} | Narkiewicz (via Lagarias) |
| 3-adic orbit hit bound | #{n ≤ X : λ2^n ∈ Σ} ≤ 2X^{α₀} | Lagarias |
| Exceptional set dim | ≤ 1/2 | Lagarias |
| Improved dim bound | ≤ log₃φ ≈ 0.438 | Abram-Bolshakov-Lagarias |
| Computational verification | n ≤ 2·3^45 ≈ 5.9×10²¹ | Saye (2022) |
| Few-ones result | ≤25 ones ⇒ n ∈ {0,2,8} | Dimitrov-Howe (2021) |

---

## Computational Verification History

| Year | Author | Verified Up To |
|------|--------|----------------|
| 1978 | Gupta | n ≤ 4,373 |
| 1991 | Vardi | n ≤ 2·3²⁰ ≈ 7×10⁹ |
| 2022 | Saye | n ≤ 2·3⁴⁵ ≈ 5.9×10²¹ |

---

## Annotated Bibliography by Approach

### A) Core Statement + Early Verification

**1. Erdős (1979)** - Original problem statement
- "Some unconventional problems in number theory," Mathematics Magazine 52, 67-70
- Poses digit-2 omission question, notes examples 1, 4, 256

**2. Gupta (1978)** - First computational verification
- Univ. Beograd Publ. Elektrotehn. Fak. Ser. Mat. Fiz. No. 602-633, 151-158
- Verified n < 4374, computational sieving

**3. Vardi (1991)** - Extended computation
- *Computational Recreations in Mathematica*, Addison-Wesley
- Extended to n ≤ 7×10⁹

---

### B) Dynamical Systems / 3-adic Framework (Lagarias Line)

**4. Lagarias (2009)** - Foundational dynamical reformulation
- "Ternary expansions of powers of 2," J. London Math. Soc. 79, 562-588
- arXiv:math/0512006
- **Key results**:
  - Power-saving bound N_λ(X) ≪ X^{0.9725} (real system)
  - Bound #{n ≤ X : (λ2^n)₃ omits 2} ≤ 2X^{log₃2} (3-adic)
  - Introduces exceptional sets E(Z₃) and dimension bounds
- **Technique**: Symbolic/digit constraints + dynamical systems + fractal dimension
- **Gap**: Cannot decide if λ = 1 is exceptional

**5. Narkiewicz** - Counting bound
- Shows N₁(X) ≪ X^{log₃2} (sparse but not finite)

---

### C) Cantor-Set Intersections / Automata (Abram-Lagarias Line)

**6. Abram-Lagarias Part I** - Exceptional set structure
- arXiv:1308.3133, EMS Press publication
- **Key results**:
  - Defines E(Z₃), conjectures dim = 0
  - Builds nested approximation E^(k) → E
  - Proves dim(E) ≤ 1/2
- **Technique**: Finite automata, graph-directed fractals, spectral radii

**7. Abram-Bolshakov-Lagarias Part II** - Improved bounds
- Experimental Mathematics 26 (2017), arXiv:1508.05967
- **Key result**: Improved upper bound via automata, log₃φ ≈ 0.438 appears
- **Technique**: Explicit automaton constructions, families of multipliers

**8. Abram-Lagarias: Path Sets**
- arXiv:1207.5004
- Establishes path-set formalism (graphs/automata for digit restrictions)

**9. Abram-Lagarias: p-adic Path-Set Fractals**
- ResearchGate preprint (2013)
- Formula: dim = log_p(spectral radius)
- Closure under p-adic operations

---

### D) Exponential Diophantine / S-unit (Few-Term Results)

**10. Dimitrov-Howe (2021)** - Bounded ones classification
- arXiv:2105.06440
- **Result**: If 2^n has no digit 2 AND ≤25 ones, then n ∈ {0,2,8}
- **Technique**: Exponential Diophantine / S-unit style
- **Gap**: Full conjecture allows unbounded ones

---

### E) Large-Scale Computation

**11. Saye (2022)** - Record verification
- Journal of Integer Sequences 25, Article 22.3.4
- arXiv:2202.13256
- **Result**: Verified to n ≤ 2·3^45 ≈ 5.9×10²¹
- **Technique**: Recursive construction exploiting periodicity mod 3^k

**12. Aliyev (2023)** - Algorithmic view
- Notes on Number Theory and Discrete Mathematics 29(3), 474-485
- Doubling algorithm in base 3, pattern phenomena

---

### F) Digit-Frequency / Normality (2020-2026)

**13. Ren-Roettger (2025)** - Digit frequencies
- arXiv:2511.03861
- Studies empirical frequency of digits/blocks in (2^n)₃
- Computations to n = 10⁶, uniformity heuristics
- Treats Erdős as much weaker open case

**14. Drmota-Spiegelhofer (2025-2026)**
- Joint distribution of binary/ternary digit sums (arXiv:2501.00850)
- Elementary bounds on digital sums (arXiv:2511.15850v2)

---

### G) Shrinking Targets Literature

**16. Tseng (2008, 2010)**
- "On circle rotations and shrinking target properties"
- Criteria for hitting shrinking neighborhoods

**17. Kim (2007)**
- "Shrinking target property of irrational rotations"

**18. Fishman-Mance-Simmons-Urbański (2015)**
- Shrinking targets for Cantor series expansions

---

### H) Geometric Progressions + Cantor Sets

**19. Cui-Ma-Jiang (2022)** - Very close in spirit
- "Geometric progressions meet Cantor sets," Chaos, Solitons & Fractals 163
- **Develops algorithmic framework** for intersections of geometric progressions with digit-restricted sets
- Proves constraints like "forbidden digit must appear"
- **Highly relevant** - same genre as Erdős

**20. Marques-Trojovský (2025)**
- "Geometric Progressions meet Zeckendorf Representations"
- arXiv:2512.19586
- Periodicity/automata methods

---

## Claimed Proofs / Status Check

**Spencer (Academia.edu)** - Claimed proof (3 pages)
- "On the Erdős Ternary Digits Conjecture"
- **NOT in mainstream venues**
- Major sources still describe conjecture as open
- **Treat as unverified claim**

---

## Key People to Follow

### Automata/3-adic
- William C. Abram
- Artem Bolshakov
- Jeffrey C. Lagarias

### Computation
- Robert I. Saye

### Exponential Diophantine
- Vassil Dimitrov
- Everett W. Howe

### Digit Frequency
- Christian Roettger
- Xuyi Ren

### Shrinking Targets
- Jimmy Tseng
- Dong Han Kim

---

## Suggested Reading Order

1. **Lagarias (2009)** - Full framing, dynamical viewpoint
2. **Saye (2022)** - Best verification, modular recursion
3. **Abram-Lagarias Part I + II** - Automata/dimension program
4. **Dimitrov-Howe (2021)** - Best "few 1's" theorem
5. **Ren-Roettger (2025)** - Modern probabilistic framing

---

## Key Papers by arXiv ID

| arXiv | Authors | Topic |
|-------|---------|-------|
| math/0512006 | Lagarias | Foundational 3-adic framework |
| 1207.5004 | Abram-Lagarias | Path sets |
| 1308.3133 | Abram-Lagarias | Cantor intersections Part I |
| 1508.05967 | Abram-Bolshakov-Lagarias | Part II, automata |
| 2105.06440 | Dimitrov-Howe | Few-ones classification |
| 2202.13256 | Saye | Verification to 10²¹ |
| 2511.03861 | Ren-Roettger | Digit frequencies |
