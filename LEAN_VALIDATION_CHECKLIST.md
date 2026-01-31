# !!!!! STOP - VALIDATE BEFORE POSTING !!!!!

## MANDATORY CHECKLIST FOR ALL LEAN CODE

Before posting ANY Lean code to Zulip, MathOverflow, or anywhere public, run through this checklist. Failure to do so risks posting "AI slop" that proves nothing.

---

## 1. UNFOLD TEST

**Question:** What does the main theorem say when you unfold ALL definitions?

**Red flags:**
- Unfolds to `True`
- Unfolds to `∃ x, False → P x` (vacuously true)
- Unfolds to something trivial that doesn't mention the actual problem

**Action:** In Lean, use `#reduce` or `#check` on the theorem. Or ask Claude to unfold it manually.

---

## 2. PLACEHOLDER CHECK

**Question:** Are any definitions set to trivial placeholder values?

**Red flags:**
```lean
def something := True        -- PLACEHOLDER
def something := 0           -- PLACEHOLDER
def something := sorry       -- At least honest, but still incomplete
```

**The rule:** Every definition must be the REAL mathematical object, or explicitly marked as `sorry` (not a fake value).

---

## 3. GROUND TRUTH CONNECTION

**Question:** Does the final theorem statement reference the actual mathematical objects?

**For Erdos Ternary Digits, it MUST mention:**
- `2^n` (powers of 2)
- Base 3 / ternary
- Digit 2

**Example of GOOD final theorem:**
```lean
theorem erdos_ternary : ∃ N, ∀ n ≥ N, ∃ k, (2^n).digits 3 k = 2
```

**Example of BAD final theorem:**
```lean
theorem something_dies : ∃ d, ¬ survives seed t d  -- What is "survives"??
```

---

## 4. AXIOM AUDIT

**Question:** Which axioms are:
- Genuinely external results (OK to axiomatize)
- Things that should be proved from definitions (NOT OK)

**OK to axiomatize:**
- `padic_exp_sum_bound` (external number theory result)

**NOT OK to axiomatize:**
- `survives_imp_bias_lower` (should follow from definitions)
- `biasSum_bound` (should follow from definitions)

**Rule:** If it's about YOUR definitions, prove it. If it's from the literature, cite and axiomatize.

---

## 5. CONSISTENCY CHECK

**Question:** Are the axioms mutually consistent with the definitions?

**Red flag example:**
```lean
def biasSum := 0  -- Definition says it's always 0
axiom biasSum_lower : 2^d ≤ ‖biasSum‖  -- Axiom says it's ≥ 2^d
-- INCONSISTENT! This proves False.
```

**Action:** For each axiom, substitute in the actual definitions and check if the statement is possible.

---

## VALIDATION PROMPT FOR CLAUDE

Copy-paste this before posting:

```
Review this Lean code for "AI slop" issues before I post it publicly.

Check:
1. UNFOLD TEST: What does the main theorem say when you unfold ALL definitions? Is it trivial or meaningful?

2. PLACEHOLDER CHECK: Are any definitions set to trivial values (:= True, := 0, := sorry)?

3. GROUND TRUTH: Does the final theorem reference actual mathematical objects from the problem?

4. AXIOM AUDIT: Which axioms are genuinely external vs. should be proved?

5. CONSISTENCY: Are axioms consistent with definitions?

Tell me if this code proves what I think it proves, or something vacuous.

[PASTE CODE HERE]
```

---

## LESSONS LEARNED (January 30, 2026)

- Posted Lean code to Zulip claiming potential Erdos solution
- Kevin Buzzard deleted it as "AI slop"
- The code proved a theorem, but NOT the Erdos conjecture
- `survives := True` and `biasSum := 0` were placeholders
- The "proof" was vacuous because it wasn't connected to the real problem
- Aristotle (Harmonic) validates syntax, not mathematical content
- A file can compile perfectly and still prove nothing useful

**Never again.**
