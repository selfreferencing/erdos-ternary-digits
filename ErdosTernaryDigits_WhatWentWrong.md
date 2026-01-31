# Erdős Ternary Digits: What Went Wrong

**Date:** January 30, 2026
**Project:** Attempted Fourier analysis proof of Erdős ternary digits conjecture
**Outcome:** Failed. Multiple mathematical errors discovered after public posting.

---

## The Conjecture

Every sufficiently large power of 2 contains the digit 2 in its base-3 representation.

Open since 1979 (47 years). Connected to Busy Beaver problem.

---

## The Attempted Approach

1. Model digit avoidance as a finite-state automaton with 3^14 states
2. Claim: Fourier transform supported on only 3^14 modes (constant in d)
3. Apply p-adic exponential sum bounds: |S_d| ≤ C·(√3)^d
4. Triangle inequality: |Δ| ≤ C'·(√3)^d
5. Survival requires |Δ| ≥ 2^d
6. Since √3 < 2, contradiction at large d

---

## What Happened

### Timeline

1. **Development phase:** Built Fourier analysis argument with AI assistance (Claude, ChatGPT)
2. **Lean formalization:** Created `ErdosTernaryFourier.lean` with Aristotle (Harmonic)
3. **Compilation:** File compiled successfully after fixing Mathlib API issues
4. **Zulip posting:** Posted to #maths asking "Is this a solution to Erdős ternary digits?"
5. **Immediate reaction:** Eye rolls, face palms
6. **Deletion:** Kevin Buzzard deleted post, DMed explanation
7. **Post-mortem:** GPT review revealed multiple fundamental mathematical errors

### Buzzard's Feedback

> "The Lean code is absolute junk; it does not prove what you are claiming/hoping it proves; the main theorem, when unfolded, becomes the tautology True by definition."

> "Posting AI-generated code and asking for review is against the terms and conditions of this Zulip and is a suspendable offence."

---

## The Four Fatal Errors

### Error 1: Order of g is Wrong

**Claim:** g = 4^(3^13) has order 3^d in (Z/3^(15+d)Z)×

**Reality:** Order is 3^(d+1), not 3^d

**The math:**
```
v_3(g - 1) = v_3(4^(3^13) - 1) = v_3(4-1) + v_3(3^13) = 1 + 13 = 14
g ≡ 1 (mod 3^14), g ≢ 1 (mod 3^15)
Subgroup (1 + 3^14 Z)/(3^(15+d) Z) has size 3^((15+d)-14) = 3^(d+1)
```

**Origin:** `GPT_PROMPT_gap_closure.md` - LTE formula correct, order inference wrong

**Impact:** Entire orbit structure is off by factor of 3

---

### Error 2: "3^14 Fourier Modes" is Unjustified

**Claim:** Automaton has 3^14 states → Fourier support ≤ 3^14

**Reality:** State complexity ≠ Fourier sparsity. These are different concepts.

**The conflation:**
- "Finite state automaton" describes computational complexity
- "Fourier support" describes spectral structure
- One does NOT imply the other without proof

**Origin:** `ErdosTernaryFourier.lean` - AI (Aristotle) made this leap without justification

**Impact:** The "constant number of modes" claim is the heart of the argument. If it fails, everything fails.

---

### Error 3: Exponential Sum Bound is FALSE as Stated

**Claim:** |S_d(A,ψ)| ≤ C·(√3)^d for all nontrivial ψ

**Reality:** FALSE. Low-conductor characters give |S_d| = 3^d.

**Counterexample:**
```
Let ψ(x) = e^(2πix/3^14) (factors through Z/3^14 Z)
Since g ≡ 1 (mod 3^14), we have ψ(A·g^t) = ψ(A) for all t
S_d(A,ψ) = Σ_{t=0}^{3^d-1} ψ(A) = 3^d · ψ(A)
|S_d| = 3^d >> C·(√3)^d
```

**Origin:** `ErdosTernaryFourier.lean` - Cited Cochrane-Zheng but ignored conductor requirements

**Impact:** The exponential sum bound, as stated, is trivially false. Would have been caught by any expert immediately.

---

### Error 4: Survival → |Δ| ≥ 2^d is Undefined and Unproven

**Claim:** If t survives to depth d, then |biasSum| ≥ 2^d

**Reality:**
- biasSum was defined as `def biasSum := 0` (placeholder!)
- No actual definition connecting to digit structure
- No proof, just axiomatized

**Origin:** `ErdosTernaryFourier.lean` - Stated as axiom without justification

**Impact:** Combined with placeholder definitions, the axiom created an inconsistent system that could prove anything.

---

## The Lean Formalization Failure

### The Placeholders

```lean
def survives (seed t d : ℕ) : Prop := True   -- PLACEHOLDER
def biasSum (seed t d : ℕ) : ℂ := 0          -- PLACEHOLDER
```

### The Inconsistency

- `survives := True` means survival is always true
- `biasSum := 0` means bias is always 0
- Axiom claims: `survives → |biasSum| ≥ 2^d`
- Substituting: `True → 2^d ≤ 0`
- This is FALSE, so the axiom system is inconsistent
- From inconsistency, Lean can prove anything

### What Lean Actually Proved

```lean
theorem fixed_t_eventually_dies : ∃ d, ¬ survives seed t d
```

Unfolds to: `∃ d, ¬ True` = `∃ d, False` = `False`

The theorem claims `False`, which is only provable from an inconsistent axiom system. **The proof is vacuous.**

---

## Why the Errors Weren't Caught Earlier

### 1. AI Confidence

Both Claude and ChatGPT produced plausible-sounding mathematical claims without verification. The claims cited real theorems (Cochrane-Zheng, LTE) but misapplied them.

### 2. Lean Type-Checking ≠ Mathematical Correctness

Lean verified that the proof type-checks. It cannot verify:
- That definitions match intended meanings
- That axioms are consistent
- That the theorem is non-trivial
- That it connects to the actual problem

### 3. Placeholder Definitions Hid the Disconnect

Using `survives := True` allowed the code to compile while completely disconnecting from the actual digit problem. This is the "AI slop" pattern Buzzard identified.

### 4. No Small Case Verification

Never computed S_d for d=1,2,3 with specific characters. Would have immediately revealed the low-conductor counterexample.

### 5. No Domain Expert Review

Relied entirely on AI judgment for analytic number theory claims. Neither the human nor the AIs are experts in this area.

---

## The Error Propagation Chain

```
GPT prompt files
    ↓ Unverified claims entered (g order, 3^14 modes)

AI-generated Lean code (Aristotle)
    ↓ Propagated claims without verification
    ↓ Added placeholder definitions
    ↓ Axiomatized unproven bridge lemmas

Lean compilation
    ↓ Type-checked successfully
    ↓ Created false confidence

Human review (me, Claude)
    ↓ Didn't catch placeholders as fatal
    ↓ Didn't verify small cases
    ↓ Didn't check conductor requirements

Public posting
    ↓ Deleted within hours
    ↓ Expert immediately identified as vacuous
```

---

## Lessons Learned

### For Lean Formalization

1. **Never use placeholder definitions** (`def X := True`, `def X := 0`)
2. **Final theorem must mention actual mathematical objects** (2^n, digits, base 3)
3. **Unfold all definitions** before claiming a proof
4. **Axioms must be consistent** with definitions (substitute and check)

### For Mathematical Claims

1. **Verify index arithmetic** with explicit calculation
2. **Don't conflate concepts** (state complexity ≠ Fourier sparsity)
3. **Check hidden conditions** in cited theorems (conductor, primitivity)
4. **Test small cases** before building large structures
5. **"Too short" is a red flag** for hard open problems

### For AI-Assisted Mathematics

1. **AI generates plausible claims, not verified ones**
2. **Compilation ≠ correctness**
3. **Get independent AI review** before posting (GPT caught what Claude missed)
4. **Create validation checklists** and run them systematically

---

## Files Created From This Failure

- `LEAN_VALIDATION_CHECKLIST.md` - 5-point Lean code check
- `BULLETPROOF_VALIDATION.md` - Full validation protocol
- `GPT_REVIEW_PROMPT.md` - AI review template
- `LEAN_FIX_PLAN.md` - What real formalization would require
- `ErdosTernaryDigits_WhatWentWrong.md` - This document

---

## Status of the Erdős Ternary Digits Conjecture

**Still open.** Our approach has fundamental flaws that cannot be easily fixed:

1. The "3^14 modes" claim is probably false
2. The exponential sum bound needs conductor restrictions
3. Even with fixes, the argument may be "too short" for a 47-year problem

The mathematical question remains: **Does a Fourier analysis approach work at all?** We don't know. But this particular formulation does not.

---

## Final Note

This was a learning experience in human-AI collaboration on hard mathematics. The failure modes are now documented and can be avoided in future work.

The embarrassment was contained:
- Zulip post was deleted (few saw it)
- Buzzard DMed privately (not publicly shamed)
- No preprint was posted
- No claims were made beyond asking for review

The correct response is to learn from it and apply better validation in the future.
