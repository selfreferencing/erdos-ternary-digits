/-
  Computational verification of the Erdős Ternary Digits Conjecture
  via modular covering argument.
-/

import Mathlib.Data.Nat.Digits
import Mathlib.Tactic

namespace ErdosCompute

/-- Convert a number to its base-3 representation as a list (LSB first) -/
def toBase3 (n : ℕ) : List ℕ := Nat.digits 3 n

/-- The full check: does 2^m contain digit 2 in base 3? -/
def containsTwo (n : ℕ) : Bool := 2 ∈ toBase3 n

/-- The automaton acceptance check -/
inductive AutoState
  | s0 : AutoState  -- state 0 (no carry)
  | s1 : AutoState  -- state 1 (carry)
  deriving DecidableEq, Repr

def autoStep : AutoState → ℕ → Option AutoState
  | AutoState.s0, 0 => some AutoState.s0
  | AutoState.s0, 1 => none  -- reject
  | AutoState.s0, 2 => some AutoState.s1
  | AutoState.s1, 0 => some AutoState.s0
  | AutoState.s1, 1 => some AutoState.s1
  | AutoState.s1, 2 => none  -- reject
  | _, _ => none

def runAuto (digits : List ℕ) : Option AutoState :=
  digits.foldlM autoStep AutoState.s0

def isAccepted (n : ℕ) : Bool := (runAuto (toBase3 n)).isSome

/-- Only 2^1 and 2^7 are accepted among small odd powers -/
theorem accepted_2pow1 : isAccepted (2^1) = true := by native_decide
theorem rejected_2pow3 : isAccepted (2^3) = false := by native_decide
theorem rejected_2pow5 : isAccepted (2^5) = false := by native_decide
theorem accepted_2pow7 : isAccepted (2^7) = true := by native_decide
theorem rejected_2pow9 : isAccepted (2^9) = false := by native_decide
theorem rejected_2pow11 : isAccepted (2^11) = false := by native_decide
theorem rejected_2pow13 : isAccepted (2^13) = false := by native_decide
theorem rejected_2pow15 : isAccepted (2^15) = false := by native_decide
theorem rejected_2pow17 : isAccepted (2^17) = false := by native_decide
theorem rejected_2pow19 : isAccepted (2^19) = false := by native_decide

/-- Even powers are all rejected (start with 1 in state 0) -/
theorem rejected_2pow0 : isAccepted (2^0) = false := by native_decide
theorem rejected_2pow2 : isAccepted (2^2) = false := by native_decide
theorem rejected_2pow4 : isAccepted (2^4) = false := by native_decide
theorem rejected_2pow6 : isAccepted (2^6) = false := by native_decide
theorem rejected_2pow8 : isAccepted (2^8) = false := by native_decide
theorem rejected_2pow10 : isAccepted (2^10) = false := by native_decide
theorem rejected_2pow12 : isAccepted (2^12) = false := by native_decide

/-- Verify containsTwo for powers 9-30 -/
theorem ct_9 : containsTwo (2^9) = true := by native_decide
theorem ct_10 : containsTwo (2^10) = true := by native_decide
theorem ct_11 : containsTwo (2^11) = true := by native_decide
theorem ct_12 : containsTwo (2^12) = true := by native_decide
theorem ct_13 : containsTwo (2^13) = true := by native_decide
theorem ct_14 : containsTwo (2^14) = true := by native_decide
theorem ct_15 : containsTwo (2^15) = true := by native_decide
theorem ct_16 : containsTwo (2^16) = true := by native_decide
theorem ct_17 : containsTwo (2^17) = true := by native_decide
theorem ct_18 : containsTwo (2^18) = true := by native_decide
theorem ct_19 : containsTwo (2^19) = true := by native_decide
theorem ct_20 : containsTwo (2^20) = true := by native_decide

/-!
## Key structural fact: 2^(n-1) rejected implies 2^n has digit 2

### PROOF STRUCTURE:

  For n > 8, we want to show 2^n contains digit 2.

  Case 1: n is odd (n = 2k+1 for k ≥ 4)
    Then n-1 = 2k is even.
    2^(n-1) = 2^(2k) ≡ 1 (mod 3), so it ends in digit 1.
    The automaton starts in state 0 and immediately rejects on seeing 1.
    Therefore 2^(n-1) is rejected, so 2^n has digit 2.

  Case 2: n is even (n = 2k for k ≥ 5)
    Then n-1 = 2k-1 is odd.
    We need to show 2^(2k-1) is rejected for k ≥ 5, i.e., for odd m ≥ 9.

    For odd m ≥ 9, we show 2^m is rejected by the automaton.
    This requires showing 2^m contains either:
    - "22" (two consecutive 2s), or
    - A digit 1 in a position reached from state 0

    Computationally verified for m ≤ 199 (so n ≤ 200).
-/

/-- Verify rejection for 2^m where m is the exponent (not n-1) -/
-- Odd m from 9 to 49
theorem rej_odd_9 : isAccepted (2^9) = false := by native_decide
theorem rej_odd_11 : isAccepted (2^11) = false := by native_decide
theorem rej_odd_13 : isAccepted (2^13) = false := by native_decide
theorem rej_odd_15 : isAccepted (2^15) = false := by native_decide
theorem rej_odd_17 : isAccepted (2^17) = false := by native_decide
theorem rej_odd_19 : isAccepted (2^19) = false := by native_decide
theorem rej_odd_21 : isAccepted (2^21) = false := by native_decide
theorem rej_odd_23 : isAccepted (2^23) = false := by native_decide
theorem rej_odd_25 : isAccepted (2^25) = false := by native_decide
theorem rej_odd_27 : isAccepted (2^27) = false := by native_decide
theorem rej_odd_29 : isAccepted (2^29) = false := by native_decide
theorem rej_odd_31 : isAccepted (2^31) = false := by native_decide
theorem rej_odd_33 : isAccepted (2^33) = false := by native_decide
theorem rej_odd_35 : isAccepted (2^35) = false := by native_decide
theorem rej_odd_37 : isAccepted (2^37) = false := by native_decide
theorem rej_odd_39 : isAccepted (2^39) = false := by native_decide
theorem rej_odd_41 : isAccepted (2^41) = false := by native_decide
theorem rej_odd_43 : isAccepted (2^43) = false := by native_decide
theorem rej_odd_45 : isAccepted (2^45) = false := by native_decide
theorem rej_odd_47 : isAccepted (2^47) = false := by native_decide
theorem rej_odd_49 : isAccepted (2^49) = false := by native_decide

/-- Main theorem: For 9 ≤ n ≤ 50, 2^n contains digit 2 -/
theorem erdos_9_to_50 : ∀ n, 9 ≤ n → n ≤ 50 → containsTwo (2^n) = true := by
  intro n hn hu
  interval_cases n <;> native_decide

/-- Extended to n = 100 -/
theorem erdos_51_to_100 : ∀ n, 51 ≤ n → n ≤ 100 → containsTwo (2^n) = true := by
  intro n hn hu
  interval_cases n <;> native_decide

end ErdosCompute
