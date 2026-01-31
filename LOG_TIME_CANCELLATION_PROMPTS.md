# Log-Time Cancellation Research Prompts

**Date:** January 30, 2026
**Purpose:** Systematic exploration of whether a "log-time cancellation theorem" exists that would resolve the Erdős ternary digits conjecture.

**Strategy:** Meta^n prompting — exploring at multiple levels of abstraction before diving into specifics.

---

## Background

The Erdős ternary digits conjecture (1979): Every sufficiently large power of 2 contains digit 2 in base 3.

**The log-time regime problem:**
- Target (digit-2-avoiding numbers) has density (2/3)^k at scale 3^k
- Available samples: O(k) values of n with 2^n having k digits
- Standard discrepancy bounds give O(1/k), but we need O((2/3)^k)
- Exponential gap between what we have and what we need

**Key insight from GPT responses:**
- The right framework is **shrinking targets / dynamical Borel-Cantelli**, not discrepancy theory
- Irrational rotations are ergodic but **not mixing** — this is the core obstruction
- The ternary Cantor set has Fourier resonances at powers of 3 (adversarial)
- The problem is in the "arithmetic exceptional" world, not the "generic" world

---

## Level (c) Prompts: Meta-Meta (Philosophy of Mathematical Discovery)

### Prompt 1: Coherence Assessment

```
I'm exploring whether a certain type of mathematical theorem might exist. Before searching for it, I want to understand the methodology of mathematical discovery itself.

**The hypothetical theorem type**: "Log-time cancellation" — a result saying that when you sample an equidistributed sequence at only logarithmically many points (relative to the modulus), structured zero-measure targets are hit only finitely often.

**Concrete instance**: The sequence {n · log₃(2) mod 1} for irrational α is equidistributed. If α = log₃(2), does this orbit hit the ternary Cantor set C₃ = {x ∈ [0,1] : ternary expansion uses only digits 0,1} only finitely often? (This is equivalent to the Erdős ternary digits conjecture from 1979, still open.)

**My meta-meta questions**:

1. How do mathematicians determine whether a novel theorem-type is coherent vs. a category error? What are the signs that a question is well-posed?

2. When exploring uncharted territory, how do you distinguish between:
   - "This theorem doesn't exist because no one has proved it yet"
   - "This theorem doesn't exist because it's false"
   - "This theorem doesn't exist because the question is malformed"

3. What's the historical methodology for discovering new theorem-types? How did discrepancy theory, ergodic theory, or Hausdorff dimension theory get "discovered" as coherent frameworks?

4. For my specific case: The standard approach (equidistribution + Weyl sums) gives error O(1/N) for N samples, but I need error O((2/3)^k) with only O(k) samples—an exponential gap. Is asking for "log-time cancellation" like asking for a perpetual motion machine (violating something fundamental), or like asking for a faster algorithm (hard but not impossible)?

I'm not asking you to solve the math problem. I'm asking: how should I think about whether this theorem-type is even the right thing to look for?
```

---

## Level (b) Prompts: Meta (Mapping the Landscape)

### Prompt 2: Field Identification

```
I'm searching for a hypothetical "log-time cancellation theorem" and need to identify which mathematical fields and techniques are relevant.

**The theorem I'm looking for**: Something that implies the following:

> When an irrational rotation orbit {n·α mod 1} is sampled at times n where the orbit has a specific "digit length" k (i.e., roughly log(3^k)/log(2) ≈ 1.58k points per digit-length), the orbit hits a structured zero-measure set (like a Cantor set defined by digit constraints) only finitely often.

**The key quantitative challenge**:
- Standard equidistribution gives discrepancy O(1/N) for N samples
- Target set has measure ~(2/3)^k at scale 3^k
- We have only O(k) = O(log(3^k)) samples per scale
- Need discrepancy < (2/3)^k with only O(k) samples — exponential gap

**My meta-questions**:

1. **What fields might own this question?**
   - Ergodic theory (dynamics on fractals, x2 x3 problems)?
   - Diophantine approximation (hitting times, shrinking targets)?
   - Fractal geometry (Hausdorff dimension of orbit intersections)?
   - Additive combinatorics (structured sets, sum-product)?

2. **What are the standard proof templates in these fields?**
   - What techniques do they use for "almost all" results?
   - What techniques work for specific orbits (not just generic ones)?

3. **What analogous theorems exist?** I'm aware of:
   - Furstenberg's x2 x3 conjecture (Rudolph-Johnson for positive entropy)
   - Lagarias (2009): exceptional set for 3-adic Cantor hits has Hausdorff dim ≤ 1/2
   - Baker's theorem on linear forms in logarithms
   - Marstrand's projection/intersection theorems
   - Schmidt's games for badly approximable numbers

   Are any of these "log-time" results? Do any control specific orbits rather than generic ones?

4. **Who are the experts I should consult or whose papers I should read?**
   - Lagarias, Hochman, Shmerkin, Bugeaud — anyone else?

5. **What would count as evidence for/against existence?**
   - For: A proof for any non-trivial special case
   - Against: A counterexample orbit, or a proof that typical irrationals hit typical Cantor sets infinitely often

Help me map the landscape before I dive into specifics.
```

---

## Level (a) Prompts: Direct (Specific Theorems)

### Prompt 3: Direct Search

```
I'm looking for a specific theorem or technique that would resolve the Erdős ternary digits conjecture (1979, still open).

**The conjecture**: For all n > 8, the base-3 representation of 2^n contains at least one digit 2.

**Equivalent formulation**: Let C₃ = {x ∈ [0,1] : ternary expansion uses only digits 0,1} (the ternary Cantor set, measure 0, Hausdorff dimension log(2)/log(3) ≈ 0.63).

The sequence {n · log₃(2) mod 1} for n = 1, 2, 3, ... is equidistributed on [0,1] by Weyl's theorem.

The conjecture is equivalent to: **this specific orbit hits C₃ only finitely often** (at n = 0, 2, 8).

**What's known**:
- Computationally verified up to n ~ 6 × 10²¹ (Saye, 2022)
- Lagarias (2009): The set of 3-adic starting points λ with infinitely many λ·2^n avoiding digit 2 has Hausdorff dimension ≤ 1/2. Conjectured: dimension 0.
- Digit frequency results: ternary digits of 2^n approach uniform distribution (1/3 each) asymptotically.

**What I'm looking for**:

1. **Is there a theorem about equidistribution with respect to fractal/Cantor targets** rather than intervals? Something that would say: structured zero-measure sets are hit only finitely by typical orbits?

2. **Is there a "log-time" discrepancy bound** for structured sets? Standard Weyl gives O(1/N) discrepancy for N samples. Is there any result giving better bounds when the target set has special structure (like self-similarity or digit-based definition)?

3. **Shrinking targets literature**: I know about shrinking target problems where the target measure decreases. But my targets are fixed (the Cantor set), not shrinking. Is there a connection?

4. **x2 x3 rigidity**: The Furstenberg conjecture is about measures invariant under both x2 and x3. My problem involves 2^n in base 3 — multiplication by 2 interacting with ternary structure. Is there a theorem in this area that constrains specific orbits (not just measures)?

5. **Any negative results?** Are there known examples of orbits {n·α mod 1} that hit a Cantor-type set infinitely often? What conditions on α or the Cantor set lead to this?

I'm trying to determine if the techniques to solve this exist but haven't been applied, or if genuinely new mathematics is required.
```

---

## Integration Prompt

### Prompt 4: Research Program Synthesis

```
I've been exploring whether a "log-time cancellation theorem" exists that would resolve the Erdős ternary digits conjecture. Let me synthesize what I've learned and ask for a research program.

**The problem**: Prove that 2^n contains digit 2 in base 3 for all n > 8.

**The obstacle**: All standard approaches fail because of a "log-time regime" mismatch:
- Target (digit-2-avoiding numbers) has density (2/3)^k at scale 3^k
- Available samples: O(k) values of n with 2^n having k digits
- Standard discrepancy bounds give O(1/k), but we need O((2/3)^k)
- Exponential gap between what we have and what we need

**Approaches I've ruled out**:
1. Fourier analysis on Z/3^k Z — fails because Fourier support is unbounded, and low-conductor characters break the exponential sum bounds
2. Automata/Cobham — requires a non-existent "Exponential Cobham theorem"
3. Standard equidistribution (Weyl) — wrong quantitative regime
4. Baker's theorem — controls magnitude, not digit structure

**Most promising lead**: Lagarias (2009) uses 3-adic Cantor set intersections and proves the exceptional set has dimension ≤ 1/2. But this is a "metric" result (almost all), not a "specific orbit" result.

**My synthesis questions**:

1. **Is "log-time cancellation" the right framing?** Or should I be looking for something else entirely — perhaps a structural/algebraic property of powers of 2, or a property of log₃(2)'s continued fraction?

2. **What's the minimal new result that would suffice?** If I could prove ONE new lemma, what should it be? Options:
   - A dimension-drop theorem for iterated Cantor intersections?
   - A log-time discrepancy bound for digit-constraint sets?
   - A specific-orbit theorem for badly approximable α?
   - Something about λ = 1 not being in the exceptional set?

3. **What's the most likely path to success?**
   - Extend Lagarias's dimension argument to show dim = 0?
   - Prove log₃(2) has "generic" behavior with respect to Cantor hitting?
   - Find a structural property of 2^n that prevents sustained Cantor membership?
   - Wait for the x2 x3 conjecture to be fully solved and derive consequences?

4. **Is this problem likely to be solved soon?** Given the current state of knowledge, is this a 5-year problem, a 50-year problem, or a "needs new mathematics" problem?

5. **What would a research program look like?** Give me a sequence of 3-5 sub-problems, ordered from most tractable to hardest, that would incrementally build toward a solution.

I want an honest assessment: should I work on this, or is it too hard for current methods?
```

---

## 2D Map Follow-Up Prompt

### Prompt 5: Locating the Problem in Parameter Space

```
You've clarified that my "log-time cancellation" question is well-posed but sits in the "arithmetic exceptional" world where methods are lacking.

Let me try the 2D map approach you suggested. I want to understand where exactly my problem sits and what's known nearby.

**Dynamics axis**: From "pure rotation" (no mixing) to "mixing/spectral gap"
**Target axis**: From "large Fourier coefficients" (like ternary Cantor) to "Fourier decay" (Salem sets)

Questions:

1. **What IS known in each quadrant?**
   - Mixing dynamics + Fourier-decay targets: presumably strong Borel-Cantelli?
   - Mixing dynamics + resonant targets: ???
   - Pure rotation + Fourier-decay targets: ???
   - Pure rotation + resonant targets: (my problem) — what's the state of the art?

2. **For my specific quadrant (pure rotation + resonant target):**
   - What are the strongest known results?
   - Lagarias (2009) proves Hausdorff dim ≤ 1/2 for the exceptional set. Is that the frontier?
   - Are there any "for this specific α" results for ANY α and ANY Cantor-type target?

3. **Is there a "boundary theorem"** — a result that says "if your target has Fourier decay exponent > X, then pure rotations give finite hits"? That would tell me exactly what property the ternary Cantor set is missing.

4. **What would move the problem into a solvable quadrant?**
   - Can the dynamics be "upgraded" (e.g., by considering 2^n mod 3^k as a different dynamical system)?
   - Can the target be "smoothed" while preserving the essential question?

I'm trying to locate the exact boundary of current knowledge so I can see if there's a gap to exploit.
```

---

## Gemini Deep Research Prompts

### Gemini Prompt 1: Shrinking Targets for Rotations

```
I need a comprehensive literature review on **shrinking target problems for irrational rotations on the circle/torus**.

Specifically, I'm looking for:

1. **The Fayad results**: Bassam Fayad apparently proved that torus translations have limited shrinking target properties. What exactly did he prove? What's the paper reference?

2. **Chaika-Constantine results**: Jon Chaika and David Constantine have quantitative shrinking-target results for rotations. What are the precise statements? Under what conditions do you get Borel-Cantelli-type conclusions?

3. **The MSTP vs STP distinction**: What is the "Monotone Shrinking Target Property" vs the full "Shrinking Target Property"? Which rotations have which?

4. **Diophantine conditions**: When do Diophantine properties of α (bounded partial quotients, etc.) help or hurt for shrinking target hitting?

5. **The current frontier**: What's the strongest known result for shrinking targets with pure rotations (not mixing systems)? What's the obstruction to going further?

Please provide full paper references with arXiv links where available. I'm trying to understand whether shrinking-target machinery can be adapted to fractal targets (specifically, Cantor sets defined by digit constraints).
```

### Gemini Prompt 2: Lagarias's 3-adic Work

```
I need a detailed analysis of **Jeffrey Lagarias's 2009 paper on ternary expansions of powers of 2** (J. London Math. Soc. 79(3), 562-588, 2009; arXiv:math/0512006).

Specifically:

1. **Main results**: What exactly does Lagarias prove about the exceptional set of 3-adic integers λ such that λ·2^n avoids digit 2 for infinitely many n?

2. **The Hausdorff dimension bound**: He proves dim ≤ 1/2. What's the proof technique? Is this bound believed to be sharp, or is dim = 0 conjectured?

3. **The 3-adic Cantor set framework**: How does he set up the problem dynamically? What is the map T: x → 2x on Z_3, and how does it interact with the Cantor set C_3?

4. **What would close the gap?**: Lagarias proves "almost all" (metric) results. What would be needed to prove something about the specific orbit starting from λ = 1?

5. **Subsequent work**: Has anyone improved on Lagarias's bounds since 2009? Are there follow-up papers?

6. **Connection to x2 x3**: Is there any connection to the Furstenberg x2 x3 conjecture or Rudolph-Johnson theorem?

I'm trying to understand if Lagarias's framework is the closest thing to a "solvable nearby problem" for the Erdős ternary digits conjecture.
```

### Gemini Prompt 3: Fourier Decay and Fractal Targets

```
I need a literature review on **equidistribution and hitting problems for fractal targets**, specifically focusing on the role of Fourier decay.

Key questions:

1. **Salem sets**: What is a Salem set? What is Fourier dimension? Which Cantor sets are Salem and which are not?

2. **The ternary Cantor set specifically**: What are the Fourier-analytic properties of the standard middle-third Cantor set? Does it have Fourier decay? What about the "digit Cantor sets" (restrict to digits in {0,1} in base 3)?

3. **Fractal hitting by orbits**: Are there any theorems of the form "if a fractal has Fourier decay exponent > X, then [some class of orbits] hits it only finitely often"?

4. **Hochman-Shmerkin work**: Michael Hochman and Pablo Shmerkin have deep results on x2 x3 and fractal intersections. What's relevant to the orbit-hitting question?

5. **Sum-product and additive combinatorics**: Is there a connection between hitting fractal targets and sum-product phenomena? Does the Bourgain-Katz-Tao machinery apply here?

6. **The boundary of current knowledge**: What's the strongest known result about deterministic sequences hitting Cantor-type sets? What invariant of the target (dimension, Fourier decay, entropy) is used?

Please provide specific paper references. I'm trying to understand whether there's a Fourier-decay threshold that separates "tractable" fractal targets from "intractable" ones.
```

### Gemini Prompt 4: Digit Problems and Normality

```
I need a survey of **what's known about digit constraints in exponential sequences**, particularly:

1. **The Erdős ternary digits conjecture**: Current status. What's the best computational verification? What approaches have been tried and failed?

2. **Related digit conjectures**: Are there analogous conjectures for other bases or other exponential sequences (3^n in base 2, etc.)? Which ones are solved?

3. **Connection to normality**: The digits of 2^n in base 3 are conjectured to be "normal" (uniform frequency 1/3 each). What's known? Is frequency easier than avoidance?

4. **Mahler's work**: Kurt Mahler studied digit patterns in powers. What did he prove?

5. **Bugeaud's work**: Yann Bugeaud works on Diophantine approximation and digit problems. What's relevant?

6. **The "why is this hard" explanation**: In survey articles or expository writing, how do experts explain why digit-avoidance problems for exponentials are so hard? What's the conceptual obstruction?

I'm trying to understand the landscape of digit problems and where the Erdős ternary conjecture sits in difficulty relative to solved problems.
```

---

## Usage Strategy

1. **Run Gemini prompts 1-4 in parallel** — they're independent literature searches
2. **Run the GPT meta-prompts (1-2)** first to establish framework
3. **Run the GPT direct prompts (3-5)** after digesting meta-level responses
4. **Synthesize**: Look for overlap between literature searches and conceptual analysis

**Goal**: Triangulate the exact boundary of current knowledge to identify either:
- An unexploited gap (tractable approach exists)
- Confirmation that genuinely new mathematics is needed

---

## Key Insights from Initial GPT Responses

### From Response 1A:
- The closest framework is **shrinking targets / dynamical Borel-Cantelli**, not discrepancy
- Irrational rotations are **not mixing** — this blocks the usual probabilistic intuition
- The ternary Cantor set has **Fourier resonances** at powers of 3 (adversarial)
- Need "arithmetic mixing substitute" that doesn't exist

### From Response 1B:
- **Probabilistic heuristic is sound**: k·(2/3)^k is summable, so Borel-Cantelli predicts finite hits
- **Equidistribution is the wrong primitive**: need mixing or special arithmetic structure
- **Two worlds**: "Generic α" (tractable) vs "Specific α = log₃2" (arithmetic exceptional, hard)
- **Missing invariant**: Need to specify what "structured target" means (dimension, Fourier decay, entropy)

### The 2D Map:
```
                    DYNAMICS AXIS
            ←─────────────────────────────→
            Pure rotation    Mixing/spectral gap
                 (no gap)         (gap)
    TARGET      │                    │
      AXIS      │   YOUR PROBLEM     │   Standard BC
       ↑        │   (upper-left:     │   works here
    Low         │    hard corner)    │
    Fourier     │                    │
    decay       ├────────────────────┤
       ↓        │   ???              │   Very strong
    High        │                    │   cancellation
    Fourier     │                    │
    decay       │                    │
```

---

## References Mentioned

- Lagarias (2009): arXiv:math/0512006 — "Ternary expansions of powers of 2"
- Saye (2022): JIS paper — computational verification to 10^21
- Fayad: shrinking targets for torus translations
- Chaika-Constantine: quantitative shrinking targets
- Hochman-Shmerkin: x2 x3 and fractal intersections
- Furstenberg x2 x3 conjecture, Rudolph-Johnson theorem
- Baker's theorem on linear forms in logarithms
- arXiv:2511.03861 — recent ternary digits paper
