import ErdosTernaryBase

set_option maxRecDepth 1000
set_option exponentiation.threshold 600000

namespace ErdosAnalytical

/-! ### Rejection Lemma Infrastructure (from GPT 2A)

These lemmas prove that if we're in state s1 and see digit 2, rejection occurs.
-/

@[simp] lemma runAutoFrom_nil (init : AutoState) :
    runAutoFrom [] init = some init := by
  simp [runAutoFrom]

@[simp] lemma runAutoFrom_cons (d : ℕ) (ds : List ℕ) (init : AutoState) :
    runAutoFrom (d :: ds) init = (autoStep init d) >>= fun s => runAutoFrom ds s := by
  simp [runAutoFrom]

@[simp] lemma runAutoFrom_singleton (d : ℕ) (init : AutoState) :
    runAutoFrom [d] init = autoStep init d := by
  simp [runAutoFrom]

/-- Append-splitting for `runAutoFrom` -/
lemma runAutoFrom_append (l1 l2 : List ℕ) (init : AutoState) :
    runAutoFrom (l1 ++ l2) init = (runAutoFrom l1 init) >>= fun s => runAutoFrom l2 s := by
  induction l1 generalizing init with
  | nil =>
      simp [runAutoFrom]
  | cons d ds ih =>
      cases h : autoStep init d with
      | none =>
          simp [runAutoFrom, h]
      | some s =>
          simp [runAutoFrom, h, ih]

/-- If a digit rejects immediately after a successful prefix, the whole run rejects. -/
lemma runAutoFrom_eq_none_of_step_none
    (pre suffix : List ℕ) (init s : AutoState) (d : ℕ)
    (hpre : runAutoFrom pre init = some s)
    (hstep : autoStep s d = none) :
    runAutoFrom (pre ++ d :: suffix) init = none := by
  rw [runAutoFrom_append, hpre]
  simp [runAutoFrom, List.foldlM_cons, hstep]

/-- Prepending a 0 while in s0 doesn't change the run result (s0 --0--> s0). -/
lemma run_prepend_zero_s0 (ds : List ℕ) :
    runAutoFrom (0 :: ds) AutoState.s0 = runAutoFrom ds AutoState.s0 := by
  simp [runAutoFrom_cons, autoStep]

/-- `take (n+1)` splits as `take n ++ [get n]` when `n < length`. -/
lemma take_succ_eq {α} (l : List α) (n : Nat) (h : n < l.length) :
    l.take (Nat.succ n) = l.take n ++ [l.get ⟨n, h⟩] := by
  induction l generalizing n with
  | nil =>
      cases h
  | cons a t ih =>
      cases n with
      | zero =>
          simp [List.take, List.get]
      | succ n =>
          have h' : n < t.length := Nat.lt_of_succ_lt_succ h
          specialize ih n h'
          simp only [List.take, List.get, List.cons_append]
          exact congrArg (a :: ·) ih

/-- `drop n` splits as `get n :: drop (n+1)` when `n < length`. -/
lemma drop_eq_get_cons {α} (l : List α) (n : Nat) (h : n < l.length) :
    l.drop n = l.get ⟨n, h⟩ :: l.drop (Nat.succ n) := by
  induction l generalizing n with
  | nil =>
      cases h
  | cons a t ih =>
      cases n with
      | zero =>
          simp [List.drop, List.get]
      | succ n =>
          have h' : n < t.length := Nat.lt_of_succ_lt_succ h
          specialize ih n h'
          simp only [List.drop, List.get]
          exact ih

/-- Core: if the state after `take i` is `s1` and digit `i` is `2`, starting from `s1` we reject. -/
theorem reject_on_2_from_s1_of_prefix_state
    (digits : List ℕ) (i : Nat)
    (hi : i < digits.length)
    (hdi : digits.get ⟨i, hi⟩ = 2)
    (hpre : runAutoFrom (digits.take i) AutoState.s1 = some AutoState.s1) :
    runAutoFrom digits AutoState.s1 = none := by
  have hsplit :
      runAutoFrom digits AutoState.s1 =
        (runAutoFrom (digits.take i) AutoState.s1) >>= fun s => runAutoFrom (digits.drop i) s := by
    simpa [List.take_append_drop] using
      (runAutoFrom_append (digits.take i) (digits.drop i) AutoState.s1)

  have hdrop : digits.drop i = 2 :: digits.drop (Nat.succ i) := by
    have h1 : digits.drop i = digits.get ⟨i, hi⟩ :: digits.drop (Nat.succ i) :=
      drop_eq_get_cons digits i hi
    rw [hdi] at h1
    exact h1

  have hsuf : runAutoFrom (digits.drop i) AutoState.s1 = none := by
    simp [hdrop, runAutoFrom, autoStep]

  rw [hsplit, hpre]
  simpa using hsuf

/-- If `take (n+1)` is accepted and its last digit is in `{1,2}`, then the resulting state is `s1`. -/
lemma prefix_end_s1_of_last_in_12 (digits : List ℕ) (n : Nat)
    (hn : n < digits.length)
    (hlast : digits.get ⟨n, hn⟩ ∈ ({1, 2} : Set ℕ))
    (hpre_ok : (runAutoFrom (digits.take (Nat.succ n)) AutoState.s1).isSome) :
    runAutoFrom (digits.take (Nat.succ n)) AutoState.s1 = some AutoState.s1 := by
  set d : ℕ := digits.get ⟨n, hn⟩

  have hd : d = 1 ∨ d = 2 := by
    simpa [d, Set.mem_insert_iff, Set.mem_singleton_iff] using hlast

  have htake : digits.take (Nat.succ n) = digits.take n ++ [d] := by
    simpa [d] using (take_succ_eq digits n hn)

  have hcalc :
      runAutoFrom (digits.take (Nat.succ n)) AutoState.s1 =
        (runAutoFrom (digits.take n) AutoState.s1) >>= fun s => autoStep s d := by
    simpa [htake, runAutoFrom_append, runAutoFrom_singleton]
      using (runAutoFrom_append (digits.take n) [d] AutoState.s1)

  cases hpref : runAutoFrom (digits.take n) AutoState.s1 with
  | none =>
      have hnone : runAutoFrom (digits.take (Nat.succ n)) AutoState.s1 = none := by
        simp [hcalc, hpref]
      have : False := by
        simpa [hnone] using hpre_ok
      exact False.elim this
  | some st =>
      have hrun : runAutoFrom (digits.take (Nat.succ n)) AutoState.s1 = autoStep st d := by
        simp [hcalc, hpref]
      cases hd with
      | inl hd1 =>
          cases st with
          | s0 =>
              have hnone : runAutoFrom (digits.take (Nat.succ n)) AutoState.s1 = none := by
                simp [hrun, hd1, autoStep]
              have : False := by
                simpa [hnone] using hpre_ok
              exact False.elim this
          | s1 =>
              simp [hrun, hd1, autoStep]
      | inr hd2 =>
          cases st with
          | s0 =>
              simp [hrun, hd2, autoStep]
          | s1 =>
              have hnone : runAutoFrom (digits.take (Nat.succ n)) AutoState.s1 = none := by
                simp [hrun, hd2, autoStep]
              have : False := by
                simpa [hnone] using hpre_ok
              exact False.elim this

/-- Rejection lemma: if digit i is 2 and previous digit is 1 or 2 (or i=0), reject from s1 -/
theorem reject_on_2_from_s1
    (digits : List ℕ) (i : Nat)
    (hi : i < digits.length)
    (hdi : digits.get ⟨i, hi⟩ = 2)
    (hprev_s1 : i = 0 ∨ (i > 0 ∧ digits.get ⟨i-1, by omega⟩ ∈ ({1, 2} : Set ℕ)))
    (hpre_ok : (runAutoFrom (digits.take i) AutoState.s1).isSome) :
    runAutoFrom digits AutoState.s1 = none := by
  have hpre : runAutoFrom (digits.take i) AutoState.s1 = some AutoState.s1 := by
    cases i with
    | zero =>
        simp [runAutoFrom]
    | succ n =>
        have hn : n < digits.length := Nat.lt_trans (Nat.lt_succ_self n) hi
        have hlast : digits.get ⟨n, hn⟩ ∈ ({1, 2} : Set ℕ) := by
          rcases hprev_s1 with h0 | hpos
          · cases Nat.succ_ne_zero n h0
          · simpa using hpos.2
        exact prefix_end_s1_of_last_in_12 digits n hn hlast hpre_ok
  exact reject_on_2_from_s1_of_prefix_state digits i hi hdi hpre

/-!
### GPT 3C: Unified Orbit Coverage with Seed Parameter

**Key fixes to original statement**:
1. t = 0 is a counterexample (tail would be empty)
2. Drop 13, not 14 - captures the (13,14) witness when digit14=2
3. Use seed parameter for both Case B (seed=128) and Case C (seed=2)

**Unified N(seed, t)**:
  N(seed, t) = seed * 4^(3^12) * (4^(3^13))^t

**Digit formulas** (from mod-3^16 expansions):
- digit 13 = seed % 3
- digit 14 = (seed * (t + 2)) % 3
- digit 15 = ((seed * (t + 2)) / 3 + seed * (1 + 2*t)) % 3

**Proof structure** (recursion on base-3 digits of t):
1. Case split on (seed * (t + 2)) % 3
2. If digit14 = 2: immediate witness at i=0 (pair 22, since digit13=2)
3. If digit14 = 0 and digit15 = 1: witness at i=1 (pair 01)
4. If digit14 = 1 and digit15 = 2: witness at i=1 (pair 12)
5. Otherwise: recurse on t/3 using digit shift

**Key axioms needed** (provable from LTE):
- four_pow_3_12_mod_3_15: 4^(3^12) ≡ 1 + 3^13 + 2·3^14 (mod 3^15)
- four_pow_3_13_mod_3_16: 4^(3^13) ≡ 1 + 3^14 + 2·3^15 (mod 3^16)
-/

/-- Unified N for orbit coverage: N(seed, t) = seed * 4^(3^12) * (4^(3^13))^t -/
def N_orbit (seed t : ℕ) : ℕ := seed * 4^(3^12) * (4^(3^13))^t

/-- The tail starting at digit 13 (not 14!) to capture (13,14) witness -/
def tail13 (seed t : ℕ) : List ℕ := (Nat.digits 3 (N_orbit seed t)).drop 13

/-!
### GPT 5A: Corrected Digit Formula Proofs

**Key correction**: The original digit14 and digit15 formulas were FALSE for general seed.

The CORRECT formulas are:
- digit 13 = seed % 3 (original was correct)
- digit 14 = (seed/3 + seed*(t+2)) % 3 (needs seed/3 term!)
- digit 15 = (seed/9 + (seed*(t+2))/3 + seed*(1+2t) + carry14) % 3

The simpler original formulas hold as COROLLARIES when:
- For digit14: (seed/3) % 3 = 0
- For digit15: additionally (seed/9) % 3 = 0

For our cases: seed=128 (Case B) has 128/3=42, 42%3=0 ✓; seed=2 (Case C) has 2/3=0 ✓
-/

/-- THEOREM (was axiom): Digit 13 of N_orbit is seed % 3 -/
theorem digit13_orbit (seed t : ℕ) (hseed : seed < 3^13) :
    digit (N_orbit seed t) 13 = seed % 3 := by
  -- Work mod 3^14: need N_orbit ≡ seed*(1 + 3^13) (mod 3^14)
  have hA : 4^(3^12) % 3^14 = 1 + 3^13 := four_pow_3_12_mod14
  have hBt : (4^(3^13))^t % 3^14 = 1 := Bpow_mod14 t
  -- N_orbit = seed * A * B^t ≡ seed * (1+3^13) * 1 = seed + seed*3^13 (mod 3^14)
  have hN : (N_orbit seed t) % 3^14 = (seed * (1 + 3^13)) % 3^14 := by
    unfold N_orbit
    have h1 : seed * 4^(3^12) % 3^14 = (seed * (1 + 3^13)) % 3^14 := by
      have : 4^(3^12) % 3^14 = (1 + 3^13) % 3^14 := by
        rw [hA]; exact (Nat.mod_eq_of_lt (by native_decide : 1 + 3^13 < 3^14)).symm
      calc seed * 4^(3^12) % 3^14
          = (seed % 3^14) * (4^(3^12) % 3^14) % 3^14 := by rw [Nat.mul_mod]
        _ = (seed % 3^14) * ((1 + 3^13) % 3^14) % 3^14 := by rw [this]
        _ = (seed * (1 + 3^13)) % 3^14 := by rw [← Nat.mul_mod]
    calc (seed * 4^(3^12) * (4^(3^13))^t) % 3^14
      = ((seed * 4^(3^12)) % 3^14 * ((4^(3^13))^t % 3^14)) % 3^14 := by rw [Nat.mul_mod]
      _ = ((seed * (1 + 3^13)) % 3^14 * 1) % 3^14 := by rw [h1, hBt]
      _ = (seed * (1 + 3^13)) % 3^14 := by simp
  -- Now compute digit13 using modular equivalence
  have hdig : digit (N_orbit seed t) 13 = digit (seed * (1 + 3^13)) 13 := by
    apply digit_eq_of_modEq
    exact hN
  -- Compute: seed*(1+3^13) / 3^13 = seed (since seed < 3^13)
  have hdiv : (seed * (1 + 3^13)) / 3^13 = seed := by
    have hs : seed / 3^13 = 0 := Nat.div_eq_of_lt hseed
    calc
      (seed * (1 + 3^13)) / 3^13 = (seed + seed * 3^13) / 3^13 := by ring_nf
      _ = seed / 3^13 + seed := by
          rw [Nat.add_mul_div_right seed seed (by positivity : 0 < 3^13)]
      _ = 0 + seed := by rw [hs]
      _ = seed := by ring
  rw [hdig, digit, hdiv]

/-- Alias for backward compatibility -/
theorem digit13_orbit_eq (seed t : ℕ) (hseed : seed < 3^13) :
    digit (N_orbit seed t) 13 = seed % 3 := digit13_orbit seed t hseed

/-- General digit 14 formula (GPT 5B: complete proof, valid for all seed < 3^13) -/
theorem digit14_orbit_general (seed t : ℕ) (hseed : seed < 3^13) :
    digit (N_orbit seed t) 14 = (seed / 3 + seed * (t + 2)) % 3 := by
  -- Work mod 3^15 using Nat.ModEq
  have hA : 4^(3^12) ≡ (1 + 7 * 3^13) [MOD 3^15] := by
    simpa [Nat.ModEq] using four_pow_3_12_mod15
  have hB : 4^(3^13) ≡ (1 + 3^14) [MOD 3^15] := by
    simpa [Nat.ModEq] using four_pow_3_13_mod15
  -- Linearize (1 + 3^14)^t mod 3^15
  have hx15 : 3^15 ∣ (3^14) * (3^14) := by native_decide
  have hlin : (1 + 3^14)^t ≡ 1 + t * 3^14 [MOD 3^15] :=
    pow_one_add_linear_modEq (3^15) (3^14) t hx15
  have hBt : (4^(3^13))^t ≡ 1 + t * 3^14 [MOD 3^15] := by
    have : (4^(3^13))^t ≡ (1 + 3^14)^t [MOD 3^15] := by simpa using (hB.pow t)
    exact this.trans hlin
  -- N_orbit ≡ seed * (1 + 7*3^13) * (1 + t*3^14) (mod 3^15)
  have hN : N_orbit seed t ≡ seed * ((1 + 7*3^13) * (1 + t*3^14)) [MOD 3^15] := by
    unfold N_orbit
    have h1 : seed * 4^(3^12) ≡ seed * (1 + 7*3^13) [MOD 3^15] := by
      simpa [Nat.mul_assoc] using (hA.mul_left seed)
    have h2 : seed * 4^(3^12) * (4^(3^13))^t ≡ (seed * (1 + 7*3^13)) * (1 + t*3^14) [MOD 3^15] := by
      simpa [Nat.mul_assoc] using (h1.mul hBt)
    simpa [Nat.mul_assoc] using h2
  -- Reduce digit via congruence
  have hdig := digit_congr_modPow (N_orbit seed t) (seed * ((1 + 7*3^13) * (1 + t*3^14))) 14 hN
  -- Compute digit of the representative using 7*3^13 = 3^13 + 2*3^14
  have h7 : 7 * 3^13 = 3^13 + 2 * 3^14 := by native_decide
  have hdiv : (seed + seed * 3^13) / 3^14 = seed / 3 := by
    have hdecomp : seed * 3^13 = (seed / 3) * 3^14 + (seed % 3) * 3^13 := by
      have hs : seed = (seed / 3) * 3 + seed % 3 := by
        have h := (Nat.div_add_mod seed 3).symm
        rw [Nat.mul_comm] at h
        exact h
      calc seed * 3^13 = ((seed / 3) * 3 + seed % 3) * 3^13 := by rw [← hs]
        _ = (seed / 3) * (3 * 3^13) + (seed % 3) * 3^13 := by ring
        _ = (seed / 3) * 3^14 + (seed % 3) * 3^13 := by
            rw [show 3 * 3^13 = 3^14 from by ring]
    have hremainder_lt : (seed % 3) * 3^13 + seed < 3^14 := by
      have hmod : seed % 3 < 3 := Nat.mod_lt seed (by decide)
      have hmodle : seed % 3 ≤ 2 := Nat.le_of_lt_succ (by simpa using hmod)
      have hmul : (seed % 3) * 3^13 ≤ 2 * 3^13 := Nat.mul_le_mul_right _ hmodle
      have hseedle : seed ≤ 3^13 - 1 := Nat.le_pred_of_lt hseed
      have hsumle : (seed % 3) * 3^13 + seed ≤ 2 * 3^13 + (3^13 - 1) :=
        Nat.add_le_add hmul hseedle
      have hrhs : 2 * 3^13 + (3^13 - 1) < 3^14 := by
        have hp : 0 < 3^13 := Nat.pow_pos (by decide : 0 < 3)
        have hsub : 3^13 - 1 < 3^13 := Nat.sub_lt hp (by decide)
        have hsum : 2 * 3^13 + (3^13 - 1) < 2 * 3^13 + 3^13 := Nat.add_lt_add_left hsub _
        have : 2 * 3^13 + 3^13 = 3^14 := by ring
        linarith
      exact lt_of_le_of_lt hsumle hrhs
    set P := (3 : ℕ)^13
    set Q := (3 : ℕ)^14
    calc (seed + seed * P) / Q
        = (seed + ((seed / 3) * Q + (seed % 3) * P)) / Q := by
            rw [hdecomp]
      _ = (((seed % 3) * P + seed) + (seed / 3) * Q) / Q := by
            have : seed + ((seed / 3) * Q + (seed % 3) * P) =
                ((seed % 3) * P + seed) + (seed / 3) * Q := by ring
            rw [this]
      _ = ((seed % 3) * P + seed) / Q + (seed / 3) := by
            have hpos : 0 < Q := Nat.pow_pos (by decide : 0 < 3)
            rw [Nat.add_mul_div_right _ _ hpos]
      _ = 0 + (seed / 3) := by
            rw [Nat.div_eq_of_lt hremainder_lt]
      _ = seed / 3 := by omega
  -- Final computation: use modular arithmetic to show the digit value
  -- Strategy: work mod 3^15, then extract digit 14 = (X / 3^14) % 3
  -- N_orbit ≡ seed * (1 + 7*3^13 + t*3^14 + ...) mod 3^15
  -- The cross term 7*t*3^27 ≡ 0 mod 3^15 since 27 ≥ 15
  -- So mod 3^15: seed * ((1+7*3^13)*(1+t*3^14)) ≡ seed*(1 + 7*3^13 + t*3^14) mod 3^15
  -- Then digit 14 = ((seed + seed*3^13 + seed*(t+2)*3^14) / 3^14) % 3
  --              = (seed + seed*3^13)/3^14 + seed*(t+2)) % 3
  --              = (seed/3 + seed*(t+2)) % 3
  have hstep1 : seed * ((1 + 7*3^13) * (1 + t*3^14)) ≡
      seed * (1 + 7*3^13 + t*3^14) [MOD 3^15] := by
    have hcross : 3^15 ∣ (7*3^13) * (t*3^14) := by
      have : 7*3^13 * (t*3^14) = 7 * t * 3^27 := by ring
      rw [this]
      exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 3 (by omega : 15 ≤ 27)) (7 * t)
    show seed * ((1 + 7*3^13) * (1 + t*3^14)) % 3^15 = seed * (1 + 7*3^13 + t*3^14) % 3^15
    have hexpand : (1 + 7*3^13) * (1 + t*3^14) = 1 + 7*3^13 + t*3^14 + 7*3^13*(t*3^14) := by ring
    rw [hexpand]
    rw [show seed * (1 + 7*3^13 + t*3^14 + 7*3^13*(t*3^14)) =
        seed * (1 + 7*3^13 + t*3^14) + seed * (7*3^13*(t*3^14)) from by ring]
    have hdvd_cross : 3^15 ∣ seed * (7*3^13*(t*3^14)) :=
      dvd_mul_of_dvd_right hcross seed
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd_cross,
        Nat.add_zero, Nat.mod_mod]
  have hstep2 : seed * (1 + 7*3^13 + t*3^14) ≡
      seed + seed*3^13 + seed*(t+2)*3^14 [MOD 3^15] := by
    show seed * (1 + 7*3^13 + t*3^14) % 3^15 = (seed + seed*3^13 + seed*(t+2)*3^14) % 3^15
    suffices h : seed * (1 + 7*3^13 + t*3^14) = seed + seed*3^13 + seed*(t+2)*3^14 by rw [h]
    set P := (3 : ℕ)^13
    set Q := (3 : ℕ)^14
    rw [show (7 : ℕ) * P = P + 2 * Q from h7]
    ring
  have hmod15 : seed * ((1 + 7*3^13) * (1 + t*3^14)) ≡
      seed + seed*3^13 + seed*(t+2)*3^14 [MOD 3^15] :=
    hstep1.trans hstep2
  have hdig2 : digit (seed * ((1 + 7*3^13) * (1 + t*3^14))) 14 =
      digit (seed + seed*3^13 + seed*(t+2)*3^14) 14 :=
    digit_congr_modPow _ _ 14 hmod15
  rw [hdig, hdig2]
  unfold digit
  -- Now: ((seed + seed*3^13 + seed*(t+2)*3^14) / 3^14) % 3
  set P := (3 : ℕ)^13
  set Q := (3 : ℕ)^14
  have hpos : 0 < Q := Nat.pow_pos (by decide : 0 < 3)
  rw [show seed + seed * P + seed * (t + 2) * Q = (seed + seed * P) + seed * (t + 2) * Q from by ring]
  rw [Nat.add_mul_div_right _ _ hpos, hdiv]

/-- Backward compatible alias -/
theorem digit14_orbit_correct (seed t : ℕ) (hseed : seed < 3^13) :
    digit (N_orbit seed t) 14 = (seed / 3 + seed * (t + 2)) % 3 :=
  digit14_orbit_general seed t hseed

/-!
### Specific seed corollaries for Case B (seed=128) and Case C (seed=2)
-/

/-- For seed=128: 128/3 = 42, and 42 % 3 = 0 -/
theorem seed128_div3_mod3 : (128 / 3) % 3 = 0 := by native_decide

/-- For seed=128: 128/9 = 14, and 14 % 3 = 2 ≠ 0
    NOTE: This means the simple digit15 formula does NOT directly apply to seed=128!
    However, Case B uses seed = 128*m, not seed = 128. -/
theorem seed128_div9_mod3 : (128 / 9) % 3 = 2 := by native_decide

/-- For seed=2: 2/3 = 0, so (2/3) % 3 = 0 -/
theorem seed2_div3_mod3 : (2 / 3) % 3 = 0 := by native_decide

/-- For seed=2: 2/9 = 0, so (2/9) % 3 = 0 -/
theorem seed2_div9_mod3 : (2 / 9) % 3 = 0 := by native_decide

/-- Check acceptance of a number -/
def isAccepted (n : ℕ) : Bool := (runAuto (Nat.digits 3 n)).isSome

/-- The main rejection predicate -/
def isRejected (j : ℕ) : Prop := isAccepted (2 * 4^j) = false

/-! ### Prefix Rejection Infrastructure (from GPT 2B)

Key insight: If a prefix of digits causes rejection, the full digit list rejects.
This allows us to prove rejection by showing the first 14 digits form a rejecting prefix.
-/

/-- The fixed first 13 digits of 2·4^(3 + m·3^12): matches 128 = [2,0,2,1,1] padded with zeros -/
def pref13 : List ℕ := [2, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]

/-- For m ≡ 2 (mod 3): the 14th digit is 1, giving this rejecting prefix -/
def pref14_m2 : List ℕ := pref13 ++ [1]

/-- For m ≡ 1 (mod 3): the 14th digit is 2, giving this prefix (enters s1) -/
def pref14_m1 : List ℕ := pref13 ++ [2]

/-- If `get? n = some a`, then `take (n+1) = take n ++ [a]` -/
theorem take_succ_of_get? {α : Type} :
    ∀ (l : List α) (n : ℕ) (a : α), l.get? n = some a → l.take (n+1) = l.take n ++ [a]
  | [], n, _, h => by cases n <;> cases h
  | x :: xs, 0, a, h => by simp at h; cases h; simp [List.take]
  | x :: xs, n+1, a, h => by
      have ih := take_succ_of_get? xs n a h
      simp [List.take, ih, List.cons_append]

/-- foldlM over append for Option monad -/
theorem foldlM_append_option {α β : Type} (f : α → β → Option α) (init : α) :
    ∀ (l₁ l₂ : List β),
      (List.foldlM f init (l₁ ++ l₂)) =
        (List.foldlM f init l₁) >>= fun a => List.foldlM f a l₂
  | [], l₂ => by simp only [List.nil_append, List.foldlM_nil, pure_bind]
  | b :: l₁, l₂ => by
      simp only [List.cons_append, List.foldlM_cons]
      cases hf : f init b with
      | none => simp [hf, bind, Option.bind]
      | some a =>
          simp only [hf, bind, Option.bind]
          exact foldlM_append_option f a l₁ l₂

/-- If a prefix rejects, appending more digits stays rejected -/
theorem runAuto_append_of_none {p s : List ℕ} (hp : runAuto p = none) :
    runAuto (p ++ s) = none := by
  show List.foldlM autoStep AutoState.s0 (p ++ s) = none
  rw [foldlM_append_option]
  show (List.foldlM autoStep AutoState.s0 p) >>= (fun a => List.foldlM autoStep a s) = none
  rw [show List.foldlM autoStep AutoState.s0 p = runAuto p from rfl, hp]
  rfl

/-- If runAuto rejects on take k, it rejects on the whole list -/
theorem runAuto_of_take_eq_none (ds : List ℕ) (k : ℕ) (h : runAuto (ds.take k) = none) :
    runAuto ds = none := by
  have hsplit : ds = ds.take k ++ ds.drop k := (List.take_append_drop k ds).symm
  rw [hsplit]
  exact runAuto_append_of_none h

/-- Computational verification: pref14_m2 = [2,0,2,1,1,0,0,0,0,0,0,0,0,1] rejects -/
theorem runAuto_pref14_m2 : runAuto pref14_m2 = none := by native_decide

/-- Computational verification: pref13 reaches state s0 -/
theorem runAuto_pref13 : runAuto pref13 = some AutoState.s0 := by native_decide

/-- Helper: split take at m+n = take m ++ (drop m).take n -/
lemma take_add' {α : Type*} (l : List α) (m n : ℕ) :
    l.take (m+n) = l.take m ++ (l.drop m).take n := by
  induction l generalizing m n with
  | nil => simp
  | cons a l ih =>
    cases m with
    | zero => simp
    | succ m => simpa [Nat.succ_add, List.take, List.drop] using congrArg (a :: ·) (ih m n)

/-- Computational verification: pref14_m1 = pref13 ++ [2] reaches s1 (s0 sees 2 → s1) -/
theorem runAuto_pref14_m1 : runAuto pref14_m1 = some AutoState.s1 := by native_decide

/-! ### Pref13 Periodicity Infrastructure (from GPT Prompt 3)

These lemmas establish that pref13 = digits of 128 padded with zeros,
and provide the machinery for proving take13_periodicity.
-/

/-- Computational: Nat.digits 3 128 = [2, 0, 2, 1, 1] -/
theorem digits_128 : Nat.digits 3 128 = [2, 0, 2, 1, 1] := by native_decide

/-- pref13 equals digits of 128 padded with 8 zeros -/
lemma pref13_eq_digits_append_zeros :
    pref13 = (Nat.digits 3 128) ++ List.replicate 8 0 := by
  simp [pref13, digits_128, List.replicate]

/-- pref13 has length 13 -/
lemma pref13_length : pref13.length = 13 := by decide

/-- ofDigits of pref13 equals 128 -/
lemma ofDigits_pref13 : Nat.ofDigits 3 pref13 = 128 := by native_decide

/-- All digits in pref13 are < 3 -/
lemma pref13_all_lt3 : ∀ d ∈ pref13, d < 3 := by
  intro d hd
  have h' : d ∈ Nat.digits 3 128 ∨ d ∈ List.replicate 8 0 := by
    have : d ∈ (Nat.digits 3 128 ++ List.replicate 8 0) := by
      simpa [pref13_eq_digits_append_zeros] using hd
    simpa using (List.mem_append.mp this)
  cases h' with
  | inl hL => exact Nat.digits_lt_base (b := 3) (m := 128) (hb := by decide) hL
  | inr hR =>
      have := List.mem_replicate.mp hR
      simp [this.2]

/-- Parameterized pref14: first 13 digits plus digit 13 based on m -/
def pref14_param (m : ℕ) : List ℕ := pref13 ++ [((128 * m) % 3)]

/-- All digits in pref14_param are < 3 -/
lemma pref14_param_all_lt3 (m : ℕ) : ∀ d ∈ pref14_param m, d < 3 := by
  intro d hd
  have : d ∈ pref13 ∨ d ∈ [((128 * m) % 3)] := by
    simpa [pref14_param] using (List.mem_append.mp hd)
  cases this with
  | inl h => exact pref13_all_lt3 d h
  | inr h =>
      have : d = (128 * m) % 3 := by simpa using (List.mem_singleton.mp h)
      simpa [this] using (Nat.mod_lt (128 * m) (by decide : 0 < 3))

/-- If i < n then taking n elements doesn't change get? i -/
theorem List.get?_take_of_lt {α : Type} (l : List α) (i n : ℕ) (hi : i < n) :
    (l.take n).get? i = l.get? i := by
  induction l generalizing i n with
  | nil => cases n <;> cases i <;> simp at hi ⊢
  | cons a t ih =>
      cases n with
      | zero => exact absurd hi (Nat.not_lt_zero i)
      | succ n =>
          cases i with
          | zero => simp
          | succ i => simp [ih, Nat.lt_of_succ_lt_succ hi]

/-! ### Case C Prefix Infrastructure

Case C: j = m·3^12 for m ≥ 1. First 13 digits match 2·4^0 = 2 = [2].
So: digit 0 = 2, digits 1-12 = 0.
-/

/-- The fixed first 13 digits of 2·4^(m·3^12): matches [2] padded with zeros -/
def pref13_C : List ℕ := [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- For Case C, m ≡ 2 (mod 3): the 14th digit is 1, giving this rejecting prefix -/
def pref14_C_m2 : List ℕ := pref13_C ++ [1]

/-- For Case C, m ≡ 1 (mod 3): the 14th digit is 2, entering s1 -/
def pref14_C_m1 : List ℕ := pref13_C ++ [2]

/-- Computational verification: pref13_C reaches state s0
    Trace: s0 -2→ s1 -0→ s0 -0→ s0 ... -0→ s0 -/
theorem runAuto_pref13_C : runAuto pref13_C = some AutoState.s0 := by native_decide

/-- Computational verification: pref14_C_m2 rejects (s0 sees 1) -/
theorem runAuto_pref14_C_m2 : runAuto pref14_C_m2 = none := by native_decide

/-- Computational verification: pref14_C_m1 reaches s1 (s0 sees 2) -/
theorem runAuto_pref14_C_m1 : runAuto pref14_C_m1 = some AutoState.s1 := by native_decide

/-!
## Part 5: Key Computational Verifications
-/

/-- 2 * 4^3 = 128 = [2,0,2,1,1]_3 (5 digits) -/
theorem two_times_four_cubed : 2 * 4^3 = 128 := by norm_num

/-- 128 < 3^5 = 243, so 128 has exactly 5 base-3 digits -/
theorem bound_128 : 128 < 3^5 := by norm_num

/-- 2 * 4^4 = 512 > 3^5 = 243, so has at least 6 digits -/
theorem two_times_four_fourth : 2 * 4^4 = 512 := by norm_num
theorem bound_512 : 512 > 3^5 := by norm_num

/-- j = 3 is accepted (unique non-trivial survivor) -/
theorem accepted_128 : isAccepted 128 = true := by native_decide

/-- j = 0 is accepted (trivial case: 2·4^0 = 2) -/
theorem accepted_j0 : isAccepted (2 * 4^0) = true := by native_decide

/-- Complete classification for j ∈ [0, 10] -/
theorem full_classification_0_to_10 :
    isAccepted (2 * 4^0) = true ∧   -- j = 0: accepted
    isAccepted (2 * 4^1) = false ∧  -- j = 1: rejected at pos 1
    isAccepted (2 * 4^2) = false ∧  -- j = 2: rejected at pos 3
    isAccepted (2 * 4^3) = true ∧   -- j = 3: THE UNIQUE EXCEPTION
    isAccepted (2 * 4^4) = false ∧  -- j = 4: rejected
    isAccepted (2 * 4^5) = false ∧  -- j = 5: rejected
    isAccepted (2 * 4^6) = false ∧  -- j = 6: rejected
    isAccepted (2 * 4^7) = false ∧  -- j = 7: rejected
    isAccepted (2 * 4^8) = false ∧  -- j = 8: rejected
    isAccepted (2 * 4^9) = false ∧  -- j = 9: rejected
    isAccepted (2 * 4^10) = false   -- j = 10: rejected
    := by native_decide

/-- Survivors in the computational range [0, 3^12): only {0, 3} -/
theorem survivors_0_and_3 :
    isAccepted (2 * 4^0) = true ∧
    isAccepted (2 * 4^3) = true := by native_decide

/-! ### Digit Shift Infrastructure (from GPT 3)

Key lemma: digit only depends on n mod 3^(k+1).
This allows us to prove the digit shift property for the inductive step.
-/

/-- digit n k only depends on n mod 3^(k+1) -/
theorem digit_eq_mod (n k : ℕ) : digit n k = (n % 3^(k+1)) / 3^k := by
  simp only [digit, Nat.pow_succ]
  exact (Nat.mod_mul_right_div_self n (3^k) 3).symm

/-- If n ≡ a (mod 3^(k+1)), then digit n k = digit a k -/
theorem digit_congr {n a k : ℕ} (h : n % 3^(k+1) = a % 3^(k+1)) :
    digit n k = digit a k := by
  rw [digit_eq_mod, digit_eq_mod, h]

/-- digit at position k of (a + 3^k * b) where a < 3^k equals b % 3 -/
theorem digit_add_mul_pow (a b k : ℕ) (ha : a < 3^k) :
    digit (a + 3^k * b) k = b % 3 := by
  simp only [digit]
  have hdiv : (a + 3^k * b) / 3^k = b := by
    rw [Nat.add_mul_div_left _ _ (Nat.pow_pos (by norm_num : 0 < 3))]
    simp [Nat.div_eq_of_lt ha]
  rw [hdiv]

/-- Linearization: if M ∣ p², then (1+p)^n ≡ 1 + n*p (mod M) -/
theorem one_add_pow_modEq_of_sq_dvd (M p n : ℕ) (hp : M ∣ p * p) :
    (1 + p)^n % M = (1 + n * p) % M := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hdvd : M ∣ n * p * p := by
      have h := dvd_mul_of_dvd_right hp n
      simp only [mul_comm n (p * p), mul_assoc] at h
      convert h using 1; ring
    calc (1 + p)^(n+1) % M
        = ((1 + p)^n * (1 + p)) % M := by rw [pow_succ]
      _ = ((1 + p)^n % M) * ((1 + p) % M) % M := by rw [Nat.mul_mod]
      _ = ((1 + n * p) % M) * ((1 + p) % M) % M := by rw [ih]
      _ = ((1 + n * p) * (1 + p)) % M := by rw [← Nat.mul_mod]
      _ = (1 + (n+1) * p + n * p * p) % M := by ring_nf
      _ = (1 + (n+1) * p) % M := by
          rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, add_zero, Nat.mod_mod]

/-- Concrete congruence: 4^(3^12) ≡ 1 + 3^13 (mod 3^14) (modular form) -/
theorem four_pow_3_12_mod14' : 4^(3^12) % 3^14 = (1 + 3^13) % 3^14 := by
  rw [four_pow_3_12_mod14, Nat.mod_eq_of_lt (by native_decide : 1 + 3^13 < 3^14)]

/-- Concrete congruence: 4^(3^12) ≡ 1 + 7·3^13 (mod 3^15) (modular form) -/
theorem four_pow_3_12_mod15' : 4^(3^12) % 3^15 = (1 + 7 * 3^13) % 3^15 := by
  rw [four_pow_3_12_mod15, Nat.mod_eq_of_lt (by native_decide : 1 + 7 * 3^13 < 3^15)]

/-- The digit shift property: digit 14 of N(3m') = digit 13 of N(m').
    This is the key lemma for the inductive step in Case B.

    Proof outline:
    - N(m') = 128 * 4^(m' * 3^12) ≡ 128 * (1 + m' * 3^13) (mod 3^14)
    - N(3m') = 128 * 4^(3m' * 3^12) ≡ 128 * (1 + 7m' * 3^14) (mod 3^15)
    - digit 13 of N(m') = (128*m') % 3 = (2m') % 3
    - digit 14 of N(3m') = (128*7m') % 3 = (2m') % 3 (since 7 ≡ 1 mod 3)
-/
theorem digit_shift_m0 (m' : ℕ) :
    digit (2 * 4^(3 + 3*m' * 3^12)) 14 = digit (2 * 4^(3 + m' * 3^12)) 13 := by
  -- Key constants
  have h128_mod : 128 % 3 = 2 := by native_decide
  have h7_mod : 7 % 3 = 1 := by native_decide
  have h128_lt_13 : 128 < 3^13 := by native_decide
  have h128_lt_14 : 128 < 3^14 := by native_decide

  -- Rewrite exponents
  have exp_lhs : 3 + 3 * m' * 3^12 = 3 + m' * 3^13 := by ring
  have lhs_eq : 2 * 4^(3 + 3*m' * 3^12) = 128 * 4^(m' * 3^13) := by
    rw [exp_lhs]; ring
  have rhs_eq : 2 * 4^(3 + m' * 3^12) = 128 * 4^(m' * 3^12) := by ring

  -- Divisibility for linearization lemma
  have hdiv14 : 3^14 ∣ 3^13 * 3^13 := by
    rw [← pow_add]; exact Nat.pow_dvd_pow 3 (by omega : 14 ≤ 13 + 13)
  have hdiv15 : 3^15 ∣ 3^14 * 3^14 := by
    rw [← pow_add]; exact Nat.pow_dvd_pow 3 (by omega : 15 ≤ 14 + 14)

  -- Step 1: 4^(m' * 3^12) ≡ 1 + m' * 3^13 (mod 3^14)
  have hlin_rhs : 4^(m' * 3^12) % 3^14 = (1 + m' * 3^13) % 3^14 := by
    rw [show m' * 3^12 = 3^12 * m' from by rw [Nat.mul_comm], pow_mul]
    -- Goal: (4^(3^12))^m' % 3^14 = (1 + m' * 3^13) % 3^14
    have h1 : (4^(3^12))^m' % 3^14 = (1 + 3^13)^m' % 3^14 := by
      have hbase : 4^(3^12) ≡ (1 + 3^13) [MOD 3^14] := by
        show 4^(3^12) % 3^14 = (1 + 3^13) % 3^14
        exact four_pow_3_12_mod14'
      exact Nat.ModEq.pow m' hbase
    rw [h1]
    exact one_add_pow_modEq_of_sq_dvd (3^14) (3^13) m' hdiv14

  -- Step 2: 4^(m' * 3^13) ≡ 1 + m' * 7 * 3^14 (mod 3^15)
  have hlin_lhs : 4^(m' * 3^13) % 3^15 = (1 + m' * 7 * 3^14) % 3^15 := by
    rw [show m' * 3^13 = 3^13 * m' from by rw [Nat.mul_comm], pow_mul]
    -- Goal: (4^(3^13))^m' % 3^15 = (1 + m' * 7 * 3^14) % 3^15
    -- First show 4^(3^13) ≡ 1 + 7*3^14 (mod 3^15)
    have h4_3_13 : 4^(3^13) ≡ (1 + 7 * 3^14) [MOD 3^15] := by
      show 4^(3^13) % 3^15 = (1 + 7 * 3^14) % 3^15
      rw [show (3:ℕ)^13 = 3^12 * 3 from by rw [pow_succ], pow_mul]
      -- Goal: (4^(3^12))^3 % 3^15 = (1 + 7 * 3^14) % 3^15
      have hbase15 : 4^(3^12) ≡ (1 + 7 * 3^13) [MOD 3^15] := by
        show 4^(3^12) % 3^15 = (1 + 7 * 3^13) % 3^15
        exact four_pow_3_12_mod15'
      have h1 := Nat.ModEq.pow 3 hbase15
      -- h1 : (4^(3^12))^3 ≡ (1 + 7*3^13)^3 [MOD 3^15]
      have hdiv15' : 3^15 ∣ (7 * 3^13) * (7 * 3^13) := by
        have : (7 * 3^13) * (7 * 3^13) = 49 * (3^13 * 3^13) := by ring
        rw [this, ← pow_add]
        exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 3 (by omega : 15 ≤ 13 + 13)) 49
      have hlin3 := one_add_pow_modEq_of_sq_dvd (3^15) (7 * 3^13) 3 hdiv15'
      -- hlin3 : (1 + 7*3^13)^3 ≡ 1 + 3*(7*3^13) [MOD 3^15]
      have h7eq : 1 + 7 * 3 ^ 14 = 1 + 3 * (7 * 3 ^ 13) := by
        have h14 : (3:ℕ)^14 = 3 * 3^13 := by rw [pow_succ, Nat.mul_comm]
        set P := (3:ℕ)^13
        rw [h14]; ring
      rw [h7eq]
      exact h1.trans hlin3
    -- Now lift to m'-th power
    have h1 := Nat.ModEq.pow m' h4_3_13
    -- h1 : (4^(3^13))^m' ≡ (1 + 7*3^14)^m' [MOD 3^15]
    have hdiv15' : 3^15 ∣ (7 * 3^14) * (7 * 3^14) := by
      have : (7 * 3^14) * (7 * 3^14) = 49 * (3^14 * 3^14) := by ring
      rw [this, ← pow_add]
      exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 3 (by omega : 15 ≤ 14 + 14)) 49
    have hlin := one_add_pow_modEq_of_sq_dvd (3^15) (7 * 3^14) m' hdiv15'
    -- hlin : (1+7*3^14)^m' ≡ 1 + m'*(7*3^14) [MOD 3^15]
    have htrans := h1.trans hlin
    -- htrans : (4^(3^13))^m' ≡ 1 + m'*(7*3^14) [MOD 3^15]
    show (4 ^ 3 ^ 13) ^ m' % 3 ^ 15 = (1 + m' * 7 * 3 ^ 14) % 3 ^ 15
    suffices h : 1 + m' * 7 * 3^14 = 1 + m' * (7 * 3^14) by rw [h]; exact htrans
    set Q := (3:ℕ)^14; ring

  -- Step 3: Extract digit 13 from RHS
  -- 128 * 4^(m' * 3^12) % 3^14 = 128 * (1 + m' * 3^13) % 3^14 = (128 + 128*m'*3^13) % 3^14
  -- digit 13 = (n % 3^14) / 3^13 % 3
  -- Since 128 < 3^13, we have 128 + 128*m'*3^13 = 128 + (128*m') * 3^13
  -- By digit_add_mul_pow: digit at position 13 = (128*m') % 3

  -- Step 4: Extract digit 14 from LHS
  -- 128 * 4^(m' * 3^13) % 3^15 = 128 * (1 + m'*7*3^14) % 3^15 = (128 + 128*7*m'*3^14) % 3^15
  -- digit 14 = (n % 3^15) / 3^14 % 3
  -- Since 128 < 3^14, by digit_add_mul_pow: digit at position 14 = (128*7*m') % 3

  -- Step 5: Show (128*m') % 3 = (128*7*m') % 3
  -- Since 128 ≡ 2 (mod 3) and 7 ≡ 1 (mod 3):
  -- (128*7*m') % 3 = (2*1*m') % 3 = (2*m') % 3 = (128*m') % 3

  have key_eq : (128 * m') % 3 = (128 * 7 * m') % 3 := by
    -- 128 * 7 * m' is already (128*7)*m' by left-associativity
    -- (128*7) % 3 = 2 = 128 % 3, so Nat.mul_mod makes both sides equal
    rw [Nat.mul_mod (128 * 7) m' 3, Nat.mul_mod 128 m' 3]

  -- Now prove digit 14 of LHS = digit 13 of RHS via the congruences
  -- This uses digit_congr and digit_add_mul_pow
  have h_digit13 : digit (128 * 4^(m' * 3^12)) 13 = (128 * m') % 3 := by
    -- Use congruence to replace the argument
    have hmod : 128 * 4^(m' * 3^12) ≡ 128 * (1 + m' * 3^13) [MOD 3^14] := by
      show (128 * 4^(m' * 3^12)) % 3^14 = (128 * (1 + m' * 3^13)) % 3^14
      rw [Nat.mul_mod, hlin_rhs, ← Nat.mul_mod]
    have hval : 128 * (1 + m' * 3^13) = 128 + (128 * m') * 3^13 := by
      set P := (3:ℕ)^13; ring
    have hmod' : 128 * 4^(m' * 3^12) ≡ 128 + (128 * m') * 3^13 [MOD 3^14] := by
      rw [← hval]; exact hmod
    -- Transfer digit via congruence
    have hdigcong := digit_congr_modPow (128 * 4^(m' * 3^12)) (128 + (128 * m') * 3^13) 13 hmod'
    rw [hdigcong]
    -- Now goal: digit (128 + (128 * m') * 3^13) 13 = (128 * m') % 3
    unfold digit
    have hdiv : (128 + (128 * m') * 3^13) / 3^13 = 128 * m' + 128 / 3^13 := by
      rw [Nat.add_mul_div_right 128 (128 * m') (Nat.pow_pos (by norm_num : 0 < 3))]
      omega
    rw [hdiv, Nat.div_eq_of_lt h128_lt_13, Nat.add_zero]

  have h_digit14 : digit (128 * 4^(m' * 3^13)) 14 = (128 * 7 * m') % 3 := by
    -- Use ModEq to replace 4^(m'*3^13) with (1 + m'*7*3^14) mod 3^15
    have hmod : 128 * 4^(m' * 3^13) ≡ 128 * (1 + m' * 7 * 3^14) [MOD 3^15] := by
      show (128 * 4^(m' * 3^13)) % 3^15 = (128 * (1 + m' * 7 * 3^14)) % 3^15
      rw [Nat.mul_mod, hlin_lhs, ← Nat.mul_mod]
    -- 128 * (1 + m'*7*3^14) = 128 + (128*7*m') * 3^14
    have hval : 128 * (1 + m' * 7 * 3^14) = 128 + (128 * 7 * m') * 3^14 := by
      set Q := (3:ℕ)^14; ring
    have hmod' : 128 * 4^(m' * 3^13) ≡ 128 + (128 * 7 * m') * 3^14 [MOD 3^15] := by
      rw [← hval]; exact hmod
    have hdigcong := digit_congr_modPow (128 * 4^(m' * 3^13)) (128 + (128 * 7 * m') * 3^14) 14 hmod'
    rw [hdigcong]
    unfold digit
    have hdiv : (128 + (128 * 7 * m') * 3^14) / 3^14 = 128 * 7 * m' + 128 / 3^14 := by
      rw [Nat.add_mul_div_right 128 (128 * 7 * m') (Nat.pow_pos (by norm_num : 0 < 3))]
      omega
    rw [hdiv, Nat.div_eq_of_lt h128_lt_14, Nat.add_zero]

  -- Put it all together
  calc digit (2 * 4^(3 + 3*m' * 3^12)) 14
      = digit (128 * 4^(m' * 3^13)) 14 := by rw [lhs_eq]
    _ = (128 * 7 * m') % 3 := h_digit14
    _ = (128 * m') % 3 := key_eq.symm
    _ = digit (128 * 4^(m' * 3^12)) 13 := h_digit13.symm
    _ = digit (2 * 4^(3 + m' * 3^12)) 13 := by rw [← rhs_eq]

/-!
## The Termination Axiom

This is the single remaining unproved statement in the formalization.
All other lemmas are fully proved from first principles.

### Mathematical Status

**Claim**: For every natural t and seed ∈ {128, 2}, the automaton rejects when
processing the ternary digits of N_orbit(seed, t) from position 14 onward.

**Computational verification**:
- Exhaustively verified for all t ∈ [0, 1,000,000]
- Maximum rejection depth observed: 33 (for t = 251,050)
- Depth distribution follows (2/3)^d decay exactly
- j=0 sibling is killed with probability exactly 1/3 at each depth

**Structural analysis**:
- The survivor set has exactly 2^d elements at depth d (equidistribution via LTE)
- A natural t with k ternary digits is "stuck" at j=0 sibling for d > k
- The j=0 sibling faces 1/3 death probability at each subsequent depth
- Kill events are essentially independent: survival of n rounds ≈ (2/3)^n

**Theoretical analysis**: The survivor set in Z_3 is a nonempty Cantor-like set
with |T_m| = 2^m elements at each depth m. The claim is that this set contains
no natural numbers. This is equivalent to:
- min(survivors at depth d) → ∞
- j=0 is killed infinitely often along the minimum path
- The 3-adic limit m_∞ = lim m_d has infinitely many nonzero digits

**Proof sketch** (not yet formalized):
1. An eventually-constant tail (all 0s or all 1s) would survive the automaton
2. Powers of 2 don't have eventually-constant ternary tails (they grow unboundedly)
3. The digit sequence of N_orbit(seed, t) = 2^E is equidistributed over {0,1,2}
4. Therefore the automaton eventually hits a rejection pattern

**Gap**: Step 3 requires proving ternary digits of 2^E are sufficiently "mixing".
This is related to normal number theory and Weyl equidistribution.

**Why this is hard**: Proving this rigorously requires either:
1. A state-sensitive congruence invariant showing long survival is impossible
2. p-adic analytic machinery (log/exp, self-similar set intersection)
3. Quantitative equidistribution bounds for ternary digits of powers of 2

This axiom isolates the exact arithmetic statement needed. Everything else
in the formalization is proved from first principles.

### References
- GPT Pro analysis: The orbit numbers are pure powers of 2: N_orbit(128,t) = 2^(7+2×3^12+2t×3^13)
- Computation files: natural_rejection_verification.py, j0_kill_simple.py
- Analysis summary: TERMINATION_ANALYSIS_SUMMARY.md in esc_stage8
-/

/-- **AXIOM (Termination)**: Every orbit number is rejected by the automaton.

This states that for seeds 128 (Case B) and 2 (Case C), processing the ternary
digits of N_orbit(seed, t) from position 14 onward, starting in state s1,
the automaton eventually rejects.

Mathematically equivalent to: "No natural number survives all depths in the
survivor tree T_m." The 3-adic survivors exist but contain no naturals. -/
axiom orbit_tail_rejects (seed : ℕ) (hseed : seed = 128 ∨ seed = 2) (t : ℕ) :
    runAutoFrom ((Nat.digits 3 (N_orbit seed t)).drop 14) AutoState.s1 = none

/-- Corollary: Case B orbit tails reject -/
theorem orbit_tail_rejects_caseB (t : ℕ) :
    runAutoFrom ((Nat.digits 3 (N_orbit 128 t)).drop 14) AutoState.s1 = none :=
  orbit_tail_rejects 128 (Or.inl rfl) t

/-- Corollary: Case C orbit tails reject -/
theorem orbit_tail_rejects_caseC (t : ℕ) :
    runAutoFrom ((Nat.digits 3 (N_orbit 2 t)).drop 14) AutoState.s1 = none :=
  orbit_tail_rejects 2 (Or.inr rfl) t

end ErdosAnalytical
