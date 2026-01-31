# Plan: Fix Lean Code to Match the Proof

## Current Problem

The code uses placeholder definitions:
```lean
def survives (seed t d : ℕ) : Prop := True
def biasSum (seed t d : ℕ) : ℂ := 0
```

This disconnects the proof from the actual Erdős conjecture.

---

## Phase 1: Ground Truth Definitions

### 1.1 Ternary Digits
```lean
-- Use Mathlib's Nat.digits
def ternaryDigits (n : ℕ) : List ℕ := Nat.digits 3 n

-- k-th ternary digit (0 if k exceeds length)
def ternaryDigit (n k : ℕ) : ℕ := (ternaryDigits n).getD k 0

-- n has digit 2 in positions 0..d
def hasDigitTwo (n : ℕ) (d : ℕ) : Prop := ∃ k ≤ d, ternaryDigit n k = 2
```

### 1.2 Survival (Real Definition)
```lean
-- t survives depth d means 2^t (scaled by seed) avoids digit 2 in positions 0..d
def survives (seed t d : ℕ) : Prop := ¬ hasDigitTwo (seed * 2^t) d
```

### 1.3 The Actual Conjecture
```lean
-- Erdős ternary digits conjecture
theorem erdos_ternary : ∃ N, ∀ n ≥ N, hasDigitTwo (2^n) n := sorry
```

---

## Phase 2: Automaton Structure

### 2.1 The Digit Automaton

The key insight: to compute digit k of `seed * 2^t`, we only need to track:
- The running sum mod 3^(k+1)
- The carry into position k

Define:
```lean
-- State: value mod 3^(d+1)
def automatonState (seed t d : ℕ) : ZMod (3^(d+1)) := (seed * 2^t : ℕ)

-- Transition: multiplying by 2
def automatonStep (s : ZMod (3^(d+1))) : ZMod (3^(d+1)) := 2 * s
```

### 2.2 Period of 3^14

Key lemma: The automaton state mod 3^14 has period dividing 3^14 (since 2^(3^13) ≡ 1 mod 3^14 by Lifting the Exponent).

```lean
lemma orbit_period : ∀ t, automatonState seed (t + 3^14) d ≡ automatonState seed t d [MOD 3^14]
```

This means the Fourier transform is supported on 3^14 frequencies.

---

## Phase 3: Fourier Analysis (Real Definitions)

### 3.1 Counting Survivors

```lean
-- Count survivors at depth d among t ∈ [0, 3^d)
def survivorCount (seed d : ℕ) : ℕ :=
  (Finset.range (3^d)).filter (fun t => survives seed t d) |>.card
```

### 3.2 Bias Sum (Real Definition)

The bias sum measures deviation from uniform digit distribution:
```lean
-- Root of unity ω = e^(2πi/3)
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

-- Bias for digit at position k
def digitBias (n k : ℕ) : ℂ := omega ^ (ternaryDigit n k)

-- Total bias sum
def biasSum (seed t d : ℕ) : ℂ :=
  ∑ k : Fin (d+1), digitBias (seed * 2^t) k
```

### 3.3 Bridge Lemmas (TO PROVE, not axiomatize)

```lean
-- Survival implies bias is large
lemma survives_imp_bias_lower (seed t d : ℕ) (hseed : seed = 128 ∨ seed = 2) :
    survives seed t d → (2 : ℝ) ^ d ≤ ‖biasSum seed t d‖ := by
  -- Proof: if all digits are in {0,1}, the bias sum is exactly 2^d
  sorry

-- Bias sum has Fourier representation with bounded support
lemma biasSum_fourier (seed t d : ℕ) :
    ∃ (A : (ZMod (Q d))ˣ) (S : Finset _) (c : _ → ℂ),
      S.card ≤ 3^14 ∧ biasSum seed t d = fourierModeSum d S c A := by
  -- Proof: from periodicity of automaton
  sorry
```

---

## Phase 4: Main Theorem

### 4.1 Keep the External Axiom
```lean
-- This is the only axiom - a standard result in analytic number theory
axiom padic_exp_sum_bound : ∃ C, 0 < C ∧ ∀ d A ψ, ψ ≠ 1 → ‖orbitExpSum d A ψ‖ ≤ C * (√3)^d
```

### 4.2 Prove Main Result
```lean
theorem fixed_t_eventually_dies (seed t : ℕ) (hseed : seed = 128 ∨ seed = 2) :
    ∃ d : ℕ, ¬ survives seed t d := by
  -- Now uses REAL survives definition
  -- Proof goes through because bridge lemmas are proved
  sorry

-- Derive the actual conjecture
theorem erdos_ternary : ∃ N, ∀ n ≥ N, hasDigitTwo (2^n) n := by
  -- From fixed_t_eventually_dies applied to all t
  sorry
```

---

## Work Breakdown

| Phase | Task | Difficulty | Status |
|-------|------|------------|--------|
| 1.1 | Ternary digit definitions | Easy | TODO |
| 1.2 | Real survives definition | Easy | TODO |
| 1.3 | State actual conjecture | Easy | TODO |
| 2.1 | Automaton definitions | Medium | TODO |
| 2.2 | Period lemma (LTE) | Hard | TODO |
| 3.1 | Survivor counting | Medium | TODO |
| 3.2 | Real biasSum definition | Medium | TODO |
| 3.3 | Bridge lemmas | Hard | TODO |
| 4.1 | Keep padic axiom | Done | ✓ |
| 4.2 | Main theorem | Medium | TODO |

---

## Key Question

Before starting: **Is the mathematical argument actually correct?**

The MathOverflow question should be posted first to verify:
1. Does `padic_exp_sum_bound` hold for this sum structure?
2. Is the Fourier support actually bounded by 3^14?
3. Does survival actually imply the bias lower bound?

If any of these fail mathematically, no amount of Lean work will help.

---

## Estimated Effort

- Phase 1: 1-2 hours
- Phase 2: 4-8 hours (LTE lemma is tricky)
- Phase 3: 8-16 hours (bridge lemmas are the hard part)
- Phase 4: 2-4 hours

**Total: 15-30 hours of Lean work**, assuming the math is correct.

Recommend: Post MathOverflow question first, then start Phase 1 while waiting for response.
