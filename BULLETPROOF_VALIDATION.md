# BULLETPROOF VALIDATION CHECKLIST

## Before sharing ANY mathematical work publicly, run ALL checks below.

---

# PART A: LEAN CODE VALIDATION

If you have Lean code, run these 5 checks:

## A1. UNFOLD TEST

**Question:** What does the main theorem say when you unfold ALL definitions?

**Red flags:**
- Unfolds to `True`
- Unfolds to `∃ x, False → P x` (vacuously true)
- Unfolds to something trivial

**Action:** Use `#reduce` or ask AI to unfold manually.

## A2. PLACEHOLDER CHECK

**Question:** Are any definitions set to trivial placeholder values?

**Red flags:**
```lean
def something := True        -- PLACEHOLDER
def something := 0           -- PLACEHOLDER
def something := sorry       -- Incomplete
```

**Rule:** Every definition must be the REAL mathematical object.

## A3. GROUND TRUTH CONNECTION

**Question:** Does the final theorem reference actual mathematical objects?

**For Erdős ternary:** Must mention `2^n`, base 3, digit 2
**For Erdős-Straus:** Must mention `4/n`, unit fractions
**For any problem:** The theorem should be readable by someone who knows the problem

## A4. AXIOM AUDIT

**Question:** Which axioms are genuinely external vs should be proved?

**OK to axiomatize:** Standard results from literature (with citation)
**NOT OK:** Anything about YOUR definitions

## A5. CONSISTENCY CHECK

**Question:** Are axioms consistent with definitions?

**Action:** Substitute definitions into each axiom. Is the result possible or contradictory?

---

# PART B: MATHEMATICAL VALIDATION

Even if Lean compiles, the math can be wrong. Run these checks:

## B1. INDEX ARITHMETIC VERIFICATION

**Question:** Are all index/exponent calculations correct?

**Common errors:**
- Off-by-one in modular arithmetic
- Wrong order of group elements (e.g., 3^d vs 3^(d+1))
- LTE (Lifting the Exponent) applied incorrectly

**Action:**
1. Write out the explicit calculation with all steps
2. Have a DIFFERENT AI verify the calculation independently
3. Compute numerical examples for small values

**Example check for this project:**
```
Claim: g = 4^(3^13) has order 3^d in (Z/3^(15+d)Z)×
Verify: v_3(g-1) = v_3(4-1) + v_3(3^13) = 1 + 13 = 14
So g ≡ 1 mod 3^14, g ≢ 1 mod 3^15
Order in (1 + 3^14 Z)/(3^(15+d) Z) = 3^((15+d)-14) = 3^(d+1)
CONCLUSION: Order is 3^(d+1), NOT 3^d. CLAIM FALSE.
```

## B2. CONCEPT CONFLATION CHECK

**Question:** Are you conflating different mathematical concepts?

**Common conflations:**
- "Finite state automaton" ≠ "Fourier support bounded by state count"
- "Nontrivial character" ≠ "High conductor character"
- "Depends on n mod M" ≠ "Fourier transform supported on M frequencies"
- "State complexity" ≠ "Spectral sparsity"

**Action:**
1. For each key claim, write precise definitions of ALL terms
2. Ask: "Does concept A logically imply concept B, or am I assuming it?"
3. Find a reference that explicitly proves A → B, or prove it yourself

**Example check for this project:**
```
Claim: "Automaton has 3^14 states" → "Fourier support ≤ 3^14"
Question: Does bounded state complexity imply Fourier sparsity?
Answer: NO. State complexity bounds linear representation dimension,
        not Fourier support. These are different.
CONCLUSION: Claim needs separate proof, not automatic.
```

## B3. SMALL CASE VERIFICATION

**Question:** Do key claims hold for small explicit values?

**Action:**
1. Identify the 3-5 most important claims in your argument
2. For each, compute explicit values for n=1,2,3,4,5 (or d=1,2,3)
3. Verify the claimed inequalities/equalities hold

**Example check for this project:**
```
Claim: |S_d(A,ψ)| ≤ C·(√3)^d for all nontrivial ψ

Test d=2: Compute S_2 explicitly for several ψ
- ψ with conductor 3^14: S_2 = 9·ψ(A) → |S_2| = 9 = 3^2
- Bound: C·(√3)^2 = C·3
- For C=1: 9 ≤ 3? FALSE

CONCLUSION: Bound fails for low-conductor characters.
```

## B4. HIDDEN CONDITIONS CHECK

**Question:** What conditions are implicitly assumed but not stated?

**Common hidden conditions:**
- Conductor/primitivity requirements for characters
- Coprimality assumptions
- Non-degeneracy conditions
- Convergence requirements
- "Generic" position assumptions

**Action:**
1. For each theorem/bound you cite, read the EXACT hypotheses
2. List ALL conditions required
3. Verify your setup satisfies EACH condition

**Example check for this project:**
```
Cited: "Exponential sums have square-root cancellation"

Actual theorem (Cochrane-Zheng style):
- Requires PRIMITIVE character (conductor = modulus)
- Or conductor-dependent bound

Our setup:
- Uses ALL nontrivial characters
- Includes characters with conductor 3^14 << 3^(15+d)

CONCLUSION: Hypothesis not satisfied. Theorem doesn't apply as stated.
```

## B5. "TOO SHORT" SANITY CHECK

**Question:** If this argument works, is it surprisingly short for the problem's difficulty?

**Heuristic:** If a 47-year-old open problem reduces to a 2-page argument with standard tools, something is probably wrong.

**Action:**
1. Estimate how long the full proof would be if all steps work
2. Compare to known difficulty of the problem
3. If suspiciously short, identify the step that's "doing too much work"

**Example check for this project:**
```
Claimed reduction:
- 3^14 Fourier modes (constant)
- Standard exponential sum bound
- Triangle inequality
- √3 < 2 comparison

If true: ~5 page proof of 47-year open problem
Reality: Famous problem, no known approach this direct
CONCLUSION: Probably a hidden error in "3^14 modes" claim
```

---

# PART C: VALIDATION PROMPT FOR AI REVIEW

Before posting anything, paste this into GPT-4/Claude:

```
Review this mathematical argument for errors before I share it publicly.

Check:
1. INDEX ARITHMETIC: Are all exponent/index calculations correct?
   Verify with explicit computation.

2. CONCEPT CONFLATION: Am I conflating different mathematical concepts?
   (e.g., "automaton states" vs "Fourier support")

3. SMALL CASES: Do the key claims hold for small explicit values?
   Compute n=1,2,3 or d=1,2,3 and verify.

4. HIDDEN CONDITIONS: What hypotheses am I implicitly assuming?
   (e.g., conductor requirements, primitivity, coprimality)

5. "TOO SHORT" CHECK: If this works, is it surprisingly easy
   for the problem's known difficulty?

Be brutally honest. I've been embarrassed before by posting flawed work.

[PASTE ARGUMENT HERE]
```

---

# PART D: DECISION GATE

After running Parts A, B, C:

| Result | Action |
|--------|--------|
| All checks pass | Safe to share (with appropriate hedging) |
| 1-2 minor issues | Fix issues, re-run checks, then share |
| Any major issue in B1-B4 | DO NOT SHARE until resolved |
| "Too short" flag (B5) | Treat as warning, investigate further |
| Multiple AI reviews disagree | Get human expert or don't share |

---

# LESSONS LEARNED (January 30, 2026)

## What went wrong:

1. **Index arithmetic error**: g = 4^(3^13) has order 3^(d+1), not 3^d
2. **Concept conflation**: "3^14 automaton states" ≠ "3^14 Fourier modes"
3. **Missing conductor check**: Low-conductor characters break the bound
4. **No small case testing**: Would have caught errors immediately
5. **Lean placeholders**: `survives := True` hid the disconnection from reality

## The meta-failure:

AI confidence + Lean type-checking created false sense of rigor.
Neither verified the actual mathematical content.

## The fix:

Run this ENTIRE checklist before sharing anything.
No exceptions.
