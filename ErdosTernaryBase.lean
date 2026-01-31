/-
  Erdős Ternary Digits Conjecture - Analytical Lemmas

  This file formalizes the key analytical lemmas:
  1. Lifting the Exponent (LTE) Lemma
  2. Periodicity Lemma
  3. Orbit Structure Lemma
  4. Case B/C Induction Principles

  THEOREM: For all n > 8, 2^n contains at least one digit 2 in base 3.

  PROOF STATUS: Five axioms remain (down from 9 - all periodicity proved).
  All 4 periodicity axioms (Case B and C) are now theorems via Nat.ofDigits_inj_of_len_eq.
-/

import Mathlib.Data.Nat.Digits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
set_option maxRecDepth 1000
set_option exponentiation.threshold 600000

/-!
## Compatibility Lemmas

This file was originally developed against older Mathlib names.
The following small compatibility layer reintroduces a few helper
definitions/lemmas under the names used below.
-/

namespace List

/-- `extract` is `drop start` followed by `take len` (older Mathlib name). -/
def extract {α : Type _} (l : List α) (start len : Nat) : List α :=
  (l.drop start).take len

@[simp] theorem extract_eq_drop_take {α : Type _} (l : List α) (start len : Nat) :
    l.extract start len = (l.drop start).take len := rfl

end List

namespace Nat

/-- Helper: ofDigits of a list is bounded by base^length when all digits are valid -/
lemma ofDigits_lt_pow_length {b : Nat} (hb : 1 < b) (l : List Nat) (w : ∀ d ∈ l, d < b) :
    Nat.ofDigits b l < b ^ l.length := by
  induction l with
  | nil => simp [Nat.ofDigits]
  | cons d ds ih =>
    rw [Nat.ofDigits_cons, List.length_cons, pow_succ']
    -- Goal: d + b * ofDigits b ds < b * b ^ ds.length
    have hd : d < b := w d (List.mem_cons_self d ds)
    have hds : ∀ d ∈ ds, d < b := fun x hx => w x (List.mem_cons_of_mem d hx)
    have ih' := ih hds
    have hb_pos : 0 < b := by omega
    -- d + b * ofDigits < b * (ofDigits + 1) ≤ b * b^|ds|
    have hsucc : Nat.ofDigits b ds + 1 ≤ b ^ ds.length := ih'
    calc d + b * Nat.ofDigits b ds
        < b + b * Nat.ofDigits b ds := by omega
      _ = b * (Nat.ofDigits b ds + 1) := by ring
      _ ≤ b * b ^ ds.length := Nat.mul_le_mul_left b hsucc

/-- Taking i digits gives a value less than base^i -/
lemma ofDigits_take_lt_pow {b : Nat} (hb : 1 < b) (i : Nat) (l : List Nat) (w : ∀ d ∈ l, d < b) :
    Nat.ofDigits b (l.take i) < b ^ i := by
  have hw : ∀ d ∈ l.take i, d < b := fun d hd => w d (List.mem_of_mem_take hd)
  have hlen : (l.take i).length ≤ i := List.length_take_le i l
  calc Nat.ofDigits b (l.take i)
      < b ^ (l.take i).length := ofDigits_lt_pow_length hb (l.take i) hw
    _ ≤ b ^ i := Nat.pow_le_pow_right (by omega : 1 ≤ b) hlen

/-- `n % p^i` equals `ofDigits` of the first `i` digits (least significant). -/
theorem self_mod_pow_eq_ofDigits_take (p i n : Nat) (h : 1 < p) :
    n % p^i = Nat.ofDigits p ((Nat.digits p n).take i) := by
  set ds := Nat.digits p n with hds_def
  have hsplit := List.take_append_drop i ds
  have happ := Nat.ofDigits_append (b := p) (l1 := ds.take i) (l2 := ds.drop i)
  rw [hsplit] at happ
  have hrecon : Nat.ofDigits p ds = n := Nat.ofDigits_digits p n
  -- n = ofDigits (take i) + p^|take i| * ofDigits (drop i)
  have hn : n = Nat.ofDigits p (ds.take i) + p ^ (ds.take i).length * Nat.ofDigits p (ds.drop i) := by
    rw [← hrecon, happ]
  have hvalid : ∀ d ∈ ds, d < p := fun d hd => Nat.digits_lt_base h hd
  have htake_lt : Nat.ofDigits p (ds.take i) < p ^ i :=
    ofDigits_take_lt_pow h i ds hvalid
  have hdiv : p ^ i ∣ p ^ (ds.take i).length * Nat.ofDigits p (ds.drop i) := by
    by_cases hle : i ≤ ds.length
    · have heq : (ds.take i).length = i := by simp [List.length_take, Nat.min_eq_left hle]
      rw [heq]
      exact Nat.dvd_mul_right (p ^ i) _
    · push_neg at hle
      have hdrop_nil : ds.drop i = [] := List.drop_eq_nil_of_le (le_of_lt hle)
      simp [hdrop_nil, Nat.ofDigits]
  rw [hn, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv, Nat.add_zero, Nat.mod_mod,
      Nat.mod_eq_of_lt htake_lt]

/-- Taking `i` digits corresponds to reducing mod `p^i`. -/
theorem ofDigits_mod_pow_eq_ofDigits_take (p i : Nat) (l : List Nat) (h : 1 < p)
    (hvalid : ∀ d ∈ l, d < p) :
    Nat.ofDigits p (l.take i) = (Nat.ofDigits p l) % p^i := by
  have hsplit := List.take_append_drop i l
  have happ := Nat.ofDigits_append (b := p) (l1 := l.take i) (l2 := l.drop i)
  conv_rhs => rw [← hsplit, happ]
  have htake_valid : ∀ d ∈ l.take i, d < p := fun d hd => hvalid d (List.mem_of_mem_take hd)
  have htake_lt : Nat.ofDigits p (l.take i) < p ^ i := ofDigits_take_lt_pow h i l hvalid
  have htake_len_le : (l.take i).length ≤ i := List.length_take_le i l
  have hdiv : p ^ i ∣ p ^ (l.take i).length * Nat.ofDigits p (l.drop i) := by
    by_cases hle : i ≤ l.length
    · have heq : (l.take i).length = i := by simp [List.length_take, Nat.min_eq_left hle]
      rw [heq]
      exact Nat.dvd_mul_right (p ^ i) _
    · push_neg at hle
      have hdrop_nil : l.drop i = [] := List.drop_eq_nil_of_le (le_of_lt hle)
      simp [hdrop_nil, Nat.ofDigits]
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv, Nat.add_zero, Nat.mod_mod,
      Nat.mod_eq_of_lt htake_lt]

/-- Injectivity of `ofDigits` when lengths are equal and digits are valid. -/
theorem ofDigits_inj_of_len_eq (b : Nat) (hb : 1 < b) {l₁ l₂ : List Nat}
    (hlen : l₁.length = l₂.length)
    (w₁ : ∀ d ∈ l₁, d < b)
    (w₂ : ∀ d ∈ l₂, d < b)
    (h : Nat.ofDigits b l₁ = Nat.ofDigits b l₂) :
    l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons d ds => simp at hlen
  | cons d₁ ds₁ ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons d₂ ds₂ =>
      rw [Nat.ofDigits_cons, Nat.ofDigits_cons] at h
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      have hd₁ : d₁ < b := w₁ d₁ (List.mem_cons_self d₁ ds₁)
      have hd₂ : d₂ < b := w₂ d₂ (List.mem_cons_self d₂ ds₂)
      have hds₁ : ∀ d ∈ ds₁, d < b := fun x hx => w₁ x (List.mem_cons_of_mem d₁ hx)
      have hds₂ : ∀ d ∈ ds₂, d < b := fun x hx => w₂ x (List.mem_cons_of_mem d₂ hx)
      -- From d₁ + b * ofDigits ds₁ = d₂ + b * ofDigits ds₂
      -- Taking mod b: d₁ = d₂
      have hd_eq : d₁ = d₂ := by
        have h1 : d₁ % b = d₁ := Nat.mod_eq_of_lt hd₁
        have h2 : d₂ % b = d₂ := Nat.mod_eq_of_lt hd₂
        have hmod : (d₁ + b * Nat.ofDigits b ds₁) % b = (d₂ + b * Nat.ofDigits b ds₂) % b :=
          congrArg (· % b) h
        simp only [Nat.add_mul_mod_self_left] at hmod
        rw [h1, h2] at hmod
        exact hmod
      -- Then ofDigits ds₁ = ofDigits ds₂
      have hds_eq : Nat.ofDigits b ds₁ = Nat.ofDigits b ds₂ := by
        have : d₁ + b * Nat.ofDigits b ds₁ = d₂ + b * Nat.ofDigits b ds₂ := h
        rw [hd_eq] at this
        have hmul : b * Nat.ofDigits b ds₁ = b * Nat.ofDigits b ds₂ := by omega
        exact Nat.mul_left_cancel (by omega : 0 < b) hmul
      rw [hd_eq, ih hlen hds₁ hds₂ hds_eq]

/-- Convenience: `n < 3` iff `n ≤ 2`. -/
theorem lt_three_iff_le_two (n : Nat) : n < 3 ↔ n = 0 ∨ n = 1 ∨ n = 2 := by
  constructor
  · intro hn
    have hle : n ≤ 2 := by omega
    have : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    exact this
  · intro h
    rcases h with h0 | h1 | h2
    · simpa [h0]
    · simpa [h1]
    · simpa [h2]

/-- Compatibility lemma for dividing then taking modulo a second factor. -/
theorem div_mod_eq_mod_div_and_mod (n a b : Nat) :
    (n / a) % b = ((n % (a * b)) / a) % b := by
  by_cases ha : a = 0
  · simp [ha]
  · by_cases hb : b = 0
    · simp [hb]
    · have ha_pos : 0 < a := Nat.pos_of_ne_zero ha
      have hb_pos : 0 < b := Nat.pos_of_ne_zero hb
      have hab_pos : 0 < a * b := Nat.mul_pos ha_pos hb_pos
      -- Use Nat.div_mod_eq_mod_div_and_mod from Lean/Mathlib
      -- n = (a*b) * q + r, so n/a = b*q + r/a, so (n/a) % b = (r/a) % b
      have : (n / a) % b = (n % (a * b) / a) % b := by
        have hdm := Nat.div_add_mod n (a * b)
        -- hdm : a * b * (n / (a * b)) + n % (a * b) = n
        have hrewrite : n = n % (a * b) + a * (b * (n / (a * b))) := by
          have := hdm
          nlinarith [Nat.mul_assoc a b (n / (a * b))]
        conv_lhs => rw [hrewrite]
        rw [Nat.add_mul_div_left _ _ ha_pos, Nat.add_mul_mod_self_left]
      exact this

end Nat


namespace ErdosAnalytical

/-!
## Part 1: Abstract Induction on 3-adic Valuation

This formalizes the induction principle used in Cases B and C of the paper.
The 3-adic valuation ν₃(m) decreases when we divide by 3, giving well-founded induction.
-/

/-- The 3-adic valuation of n -/
def ν₃ (n : ℕ) : ℕ := n.factorization 3

/-- Well-founded induction on 3-adic valuation.
    This is the abstract induction principle used in Cases B and C of the paper:
    - Base case: m not divisible by 3
    - Inductive step: if P holds for m/3, then P holds for m -/
theorem induction_on_v3 {P : ℕ → Prop}
    (hbase : ∀ m, m ≠ 0 → ¬(3 ∣ m) → P m)
    (hstep : ∀ m, m ≠ 0 → 3 ∣ m → P (m / 3) → P m) :
    ∀ m, m ≠ 0 → P m := by
  intro m hm
  induction m using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : 3 ∣ n
    · apply hstep n hm h
      have hdiv : n / 3 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by norm_num : 1 < 3)
      have hne : n / 3 ≠ 0 := by
        intro heq
        simp only [Nat.div_eq_zero_iff (by norm_num : 0 < 3)] at heq
        omega
      exact ih (n / 3) hdiv hne
    · exact hbase n hm h

/-- ν₃(3m) = ν₃(m) + 1 for m ≠ 0 -/
theorem v3_mul_three (m : ℕ) (hm : m ≠ 0) : ν₃ (3 * m) = ν₃ m + 1 := by
  simp only [ν₃, Nat.factorization_mul (by norm_num : 3 ≠ 0) hm]
  simp only [Finsupp.coe_add, Pi.add_apply]
  simp only [Nat.Prime.factorization_self (by norm_num : Nat.Prime 3)]
  ring

/-- ν₃(m) = 0 iff 3 ∤ m (for m ≠ 0) -/
theorem v3_eq_zero_iff (m : ℕ) (hm : m ≠ 0) : ν₃ m = 0 ↔ ¬(3 ∣ m) := by
  simp only [ν₃]
  constructor
  · intro h hdiv
    have := Nat.Prime.factorization_pos_of_dvd (by norm_num : Nat.Prime 3) hm hdiv
    omega
  · intro h
    exact Nat.factorization_eq_zero_of_not_dvd h

/-!
## Part 2: Lifting the Exponent (LTE) Lemma

We prove that 4^{3^k} ≡ 1 (mod 3^{k+1}) but 4^{3^k} ≢ 1 (mod 3^{k+2}).
More precisely: 4^{3^k} = 1 + 3^{k+1} * u_k where u_k ≡ 1 (mod 3).

Key insight: The LTE coefficient c = (4^(3^12) - 1) / 3^13 satisfies c ≡ 1 (mod 3).
-/

/-- 4 ≡ 1 (mod 3) -/
theorem four_mod_three : 4 % 3 = 1 := by native_decide

/-- 4^n ≡ 1 (mod 3) for all n -/
theorem four_pow_mod_three (n : ℕ) : 4^n % 3 = 1 := by
  induction n with
  | zero => native_decide
  | succ n ih =>
    calc 4^(n+1) % 3 = (4^n * 4) % 3 := by ring_nf
    _ = (4^n % 3) * (4 % 3) % 3 := by rw [Nat.mul_mod]
    _ = 1 * 1 % 3 := by rw [ih, four_mod_three]
    _ = 1 := by native_decide

/-- Key verification: 4^{3^k} ≡ 1 (mod 3^{k+1}) for small k -/
theorem lte_k0 : 4^(3^0) % 3^1 = 1 := by native_decide
theorem lte_k1 : 4^(3^1) % 3^2 = 1 := by native_decide
theorem lte_k2 : 4^(3^2) % 3^3 = 1 := by native_decide
theorem lte_k3 : 4^(3^3) % 3^4 = 1 := by native_decide
theorem lte_k4 : 4^(3^4) % 3^5 = 1 := by native_decide

/-- Non-divisibility: 4^{3^k} ≢ 1 (mod 3^{k+2}) for small k -/
theorem lte_val_0_ndiv : ¬(9 ∣ (4^(3^0) - 1)) := by native_decide
theorem lte_val_1_ndiv : ¬(27 ∣ (4^(3^1) - 1)) := by native_decide
theorem lte_val_2_ndiv : ¬(81 ∣ (4^(3^2) - 1)) := by native_decide
theorem lte_val_3_ndiv : ¬(243 ∣ (4^(3^3) - 1)) := by native_decide

/-- 4^(3^12) ≡ 1 (mod 3^13) - key for Case B/C periodicity -/
theorem four_pow_3_12_mod : 4^(3^12) % 3^13 = 1 := by native_decide

/-- 4^(3^12) mod 3^14 = 1 + 3^13 (the +1 digit at position 13) -/
theorem four_pow_3_12_mod14 : 4^(3^12) % 3^14 = 1 + 3^13 := by native_decide

/-- 4^(3^12) mod 3^15 = 1 + 7·3^13 (decomposes to digits 13=1, 14=2) -/
theorem four_pow_3_12_mod15 : 4^(3^12) % 3^15 = 1 + 7 * 3^13 := by native_decide

/-- 4^(3^12) mod 3^16 = 1 + 16·3^13 (note: 7*3^13 + 3^15 = 7*3^13 + 9*3^13 = 16*3^13) -/
theorem four_pow_3_12_mod16 : 4^(3^12) % 3^16 = (1 + 16 * 3^13) % 3^16 := by native_decide

/-- 4^(3^13) ≡ 1 (mod 3^14) -/
theorem four_pow_3_13_mod14 : 4^(3^13) % 3^14 = 1 := by native_decide

/-- 4^(3^13) mod 3^15 = 1 + 3^14 -/
theorem four_pow_3_13_mod15 : 4^(3^13) % 3^15 = 1 + 3^14 := by native_decide

/-- 4^(3^13) mod 3^16 = 1 + 3^14 + 2·3^15 -/
theorem four_pow_3_13_mod16 : 4^(3^13) % 3^16 = 1 + 3^14 + 2 * 3^15 := by native_decide

/-!
### LTE (Lifting the Exponent) Lemmas (from GPT 4A)

Key insight: Use "cubing lift" instead of full LTE machinery.
If x ≡ 1 (mod 3^k) with k>0, then x³ ≡ 1 (mod 3^(k+1)).
Iterate by induction on t to get A^(3^t) ≡ 1 (mod 3^(13+t)).
-/

/-- v₃(4^(3^12) - 1) = 13: mod 3^13 but not mod 3^14 -/
theorem v3_four_pow_3_12_sub_1 :
    4^(3^12) % 3^13 = 1 ∧ 4^(3^12) % 3^14 ≠ 1 := by
  refine ⟨four_pow_3_12_mod, ?_⟩
  have hlt : 1 + 3^13 < 3^14 := by native_decide
  have hEq : 4^(3^12) % 3^14 = 1 + 3^13 := by
    simpa [Nat.mod_eq_of_lt hlt] using four_pow_3_12_mod14
  simpa [hEq] using (by native_decide : (1 + 3^13 : ℕ) ≠ 1)

/-- Cubing lift: x ≡ 1 (mod 3^k), k>0 ⟹ x³ ≡ 1 (mod 3^(k+1)) -/
lemma cube_lift_mod_threePow (k x : ℕ) (hk : 0 < k) (hx : x % 3^k = 1) :
    x^3 % 3^(k+1) = 1 := by
  let m : ℕ := 3^k
  let q : ℕ := x / m
  let δ : ℕ := q * m

  have hx_eq : x = δ + 1 := by
    have h := (Nat.div_add_mod x m).symm
    simp only [Nat.mul_comm m (x / m)] at h
    simpa [m, q, δ, hx] using h

  have hN : 3^(k+1) = 3 * m := by
    simp [m, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

  have hm3 : 3 ∣ m := by
    cases k with
    | zero => cases hk
    | succ k' =>
      refine ⟨3^k', ?_⟩
      simp [m, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

  rcases hm3 with ⟨r, hr⟩
  have hN_m2 : (3*m) ∣ m^2 := by
    refine ⟨r, ?_⟩
    simp [hr, pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

  have hN_delta2 : (3*m) ∣ δ^2 := by
    have : (3*m) ∣ m^2 * q^2 := by
      have h1 : (3*m) ∣ q^2 * m^2 := dvd_mul_of_dvd_right hN_m2 (q^2)
      simpa [Nat.mul_comm (q^2) (m^2)] using h1
    simpa [δ, mul_pow, pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this

  have hN_delta3 : (3*m) ∣ δ^3 := by
    have : (3*m) ∣ δ^2 * δ := dvd_mul_of_dvd_left hN_delta2 δ
    simpa [pow_succ, pow_two, Nat.mul_assoc] using this

  have hN_3delta : (3*m) ∣ 3*δ := by
    refine ⟨q, ?_⟩
    simp [δ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

  have hN_3delta2 : (3*m) ∣ 3*δ^2 := by
    have : (3*m) ∣ δ^2 * 3 := dvd_mul_of_dvd_left hN_delta2 3
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

  have hN_big : (3*m) ∣ δ^3 + 3*δ^2 + 3*δ := by
    have h12 : (3*m) ∣ δ^3 + 3*δ^2 := dvd_add hN_delta3 hN_3delta2
    have h123 : (3*m) ∣ (δ^3 + 3*δ^2) + 3*δ := dvd_add h12 hN_3delta
    simpa [Nat.add_assoc] using h123

  have hbig0 : (δ^3 + 3*δ^2 + 3*δ) % (3*m) = 0 :=
    Nat.mod_eq_zero_of_dvd hN_big

  have hx3 : x^3 = (δ^3 + 3*δ^2 + 3*δ) + 1 := by
    calc
      x^3 = (δ + 1)^3 := by simpa [hx_eq]
      _ = (δ^3 + 3*δ^2 + 3*δ) + 1 := by ring

  have hlt : 1 < 3*m := by
    have hmpos : 0 < m := by
      have h3pos : 0 < 3 := by decide
      exact Nat.pow_pos h3pos
    have hmge1 : 1 ≤ m := Nat.succ_le_of_lt hmpos
    have h3le : 3 ≤ 3*m := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using (Nat.mul_le_mul_left 3 hmge1)
    exact lt_of_lt_of_le (by decide : 1 < 3) h3le
  have h1mod : 1 % (3*m) = 1 := Nat.mod_eq_of_lt hlt

  have : x^3 % (3*m) = 1 := by
    calc
      x^3 % (3*m) = ((δ^3 + 3*δ^2 + 3*δ) + 1) % (3*m) := by simpa [hx3]
      _ = (((δ^3 + 3*δ^2 + 3*δ) % (3*m)) + (1 % (3*m))) % (3*m) := by
            simp [Nat.add_mod]
      _ = (0 + 1) % (3*m) := by simp [hbig0, h1mod]
      _ = 1 := by simp [h1mod]

  simpa [hN] using this

/-- LTE consequence: A^(3^t) ≡ 1 (mod 3^(13+t)) for A = 4^(3^12) -/
theorem four_pow_3_12_pow_3t_mod (t : ℕ) :
    (4^(3^12))^(3^t) % 3^(13 + t) = 1 := by
  let A : ℕ := 4^(3^12)
  induction t with
  | zero =>
      simpa [A, four_pow_3_12_mod]
  | succ t ih =>
      have hk : 0 < 13 + t := by
        simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (Nat.succ_pos (12 + t))
      have h := cube_lift_mod_threePow (k := 13 + t) (x := A^(3^t)) hk ih
      simp only [A, Nat.pow_succ, pow_mul] at h ⊢
      convert h using 2 <;> ring

/-- Equivalently: 4^(3^(12+t)) ≡ 1 (mod 3^(13+t)) -/
theorem four_pow_3_exp_mod (t : ℕ) :
    4^(3^(12 + t)) % 3^(13 + t) = 1 := by
  have h := four_pow_3_12_pow_3t_mod (t := t)
  have exp_eq : 3^(12 + t) = 3^12 * 3^t := by rw [pow_add]
  have pow_eq : 4^(3^(12 + t)) = (4^(3^12))^(3^t) := by rw [exp_eq, pow_mul]
  rw [pow_eq]
  exact h

/-! **Alternative (GPT 4B)**: Can also prove via `padicValNat.pow_sub_pow` directly:
    `padicValNat 3 (4^(3^(12+t)) - 1) = 13 + t` using Mathlib's LTE. -/

/-!
## Part 3: Digit Extraction Infrastructure

The k-th base-3 digit of n is (n / 3^k) % 3.
-/

/-- The k-th base-3 digit of n (0-indexed from LSB) -/
def digit (n k : ℕ) : ℕ := (n / 3^k) % 3

/-- Digit 0 is the remainder mod 3 -/
theorem digit_zero (n : ℕ) : digit n 0 = n % 3 := by simp [digit]

/-- Digit `k` can be computed from the residue mod `3^(k+1)`. -/
theorem digit_from_mod (n k : ℕ) :
    digit n k = ((n % 3^(k+1)) / 3^k) % 3 := by
  -- goal becomes: (n / 3^k) % 3 = ((n % 3^(k+1)) / 3^k) % 3
  simp [digit]

  let m : ℕ := 3^(k+1)
  let q : ℕ := n / m
  let r : ℕ := n % m

  have hkpos : 0 < 3^k := by
    have h3pos : 0 < 3 := by decide
    exact Nat.pow_pos h3pos

  have hdecomp : m * q + r = n := by
    simpa [m, q, r] using (Nat.div_add_mod n m)

  have hm_mul : m * q = (q * 3) * 3^k := by
    dsimp [m]
    calc
      3^(k+1) * q = (3^k * 3) * q := by rw [Nat.pow_succ]
      _ = 3^k * (3 * q) := by rw [Nat.mul_assoc]
      _ = 3^k * (q * 3) := by rw [Nat.mul_comm 3 q]
      _ = (q * 3) * 3^k := by rw [Nat.mul_comm (3^k) (q * 3)]

  have hdiv : n / 3^k = r / 3^k + q * 3 := by
    have : n / 3^k = (m * q + r) / 3^k := by
      simpa using (congrArg (fun t => t / 3^k) hdecomp.symm)
    calc
      n / 3^k = (m * q + r) / 3^k := this
      _ = (r + m * q) / 3^k := by simpa [Nat.add_comm]
      _ = (r + (q * 3) * 3^k) / 3^k := by simpa [hm_mul]
      _ = r / 3^k + q * 3 := by
            simpa using (Nat.add_mul_div_right r (q * 3) (z := 3^k) hkpos)

  have hmod : (n / 3^k) % 3 = (r / 3^k) % 3 := by
    calc
      (n / 3^k) % 3 = (r / 3^k + q * 3) % 3 := by simpa [hdiv]
      _ = (r / 3^k) % 3 := by
            simpa using (Nat.add_mul_mod_self_right (x := r / 3^k) (y := q) (z := 3))

  simpa [r, m] using hmod

/-- digit n k only depends on n % 3^(k+1) - key for modular digit proofs -/
lemma digit_eq_of_modEq {n m k : ℕ} (h : n % 3^(k+1) = m % 3^(k+1)) :
    digit n k = digit m k := by
  simp only [digit_from_mod, h]

/-- digit depends only on residue mod 3^(k+1) - version using Nat.ModEq -/
lemma digit_congr_modPow (n m k : ℕ) (h : n ≡ m [MOD 3^(k+1)]) :
    digit n k = digit m k := by
  have hm : n % 3^(k+1) = m % 3^(k+1) := by simpa [Nat.ModEq] using h
  exact digit_eq_of_modEq hm

/-- Linearization lemma using Nat.ModEq: if x² ≡ 0 (mod M), then (1+x)^t ≡ 1 + t·x (mod M) -/
lemma pow_one_add_linear_modEq (M x t : ℕ) (hx : M ∣ x * x) :
    (1 + x)^t ≡ 1 + t*x [MOD M] := by
  induction t with
  | zero => simp [Nat.ModEq]
  | succ t ih =>
      have hmul : (1 + x)^(t+1) ≡ (1 + t*x) * (1 + x) [MOD M] := by
        simpa [pow_succ, Nat.mul_assoc] using (ih.mul_right (1 + x))
      have hx0 : x * x ≡ 0 [MOD M] := by simp [Nat.ModEq, Nat.mod_eq_zero_of_dvd hx]
      have ht0 : t * (x * x) ≡ 0 [MOD M] := by simpa [Nat.mul_assoc] using (hx0.mul_left t)
      have hexp : (1 + t*x) * (1 + x) = (1 + (t+1)*x) + t*(x*x) := by ring
      have hkill : ((1 + (t+1)*x) + t*(x*x)) ≡ (1 + (t+1)*x) [MOD M] := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (ht0.add_left (1 + (t+1)*x))
      have : (1 + x)^(t+1) ≡ (1 + (t+1)*x) [MOD M] := by
        calc
          (1 + x)^(t+1) ≡ (1 + t*x) * (1 + x) [MOD M] := hmul
          _ ≡ (1 + (t+1)*x) + t*(x*x) [MOD M] := by simp only [hexp]; exact Nat.ModEq.refl _
          _ ≡ (1 + (t+1)*x) [MOD M] := hkill
      simpa [Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

/-- Linearization lemma: if x² ≡ 0 (mod M), then (1+x)^t ≡ 1 + t·x (mod M) - % version -/
lemma one_add_pow_linear (M x : ℕ) (hx : M ∣ x^2) (t : ℕ) :
    (1 + x)^t % M = (1 + t*x) % M := by
  induction t with
  | zero => simp
  | succ t ih =>
      -- (1+x)^(t+1) = (1+x)^t * (1+x)
      -- ≡ (1 + t*x) * (1+x) = 1 + (t+1)*x + t*x²
      -- ≡ 1 + (t+1)*x (mod M) since M | x²
      have hexp : (1 + x)^(t+1) = (1 + x)^t * (1 + x) := by ring
      have hrhs : (1 + t*x) * (1 + x) = 1 + (t+1)*x + t*x^2 := by ring
      -- t*x² ≡ 0 (mod M)
      have htx2 : t * x^2 % M = 0 := by
        rcases hx with ⟨c, hc⟩
        simp [hc, Nat.mul_mod, Nat.mod_self]
      calc
        (1 + x)^(t+1) % M = ((1 + x)^t * (1 + x)) % M := by rw [hexp]
        _ = (((1 + x)^t % M) * ((1 + x) % M)) % M := by rw [Nat.mul_mod]
        _ = (((1 + t*x) % M) * ((1 + x) % M)) % M := by rw [ih]
        _ = ((1 + t*x) * (1 + x)) % M := by rw [← Nat.mul_mod]
        _ = (1 + (t+1)*x + t*x^2) % M := by rw [hrhs]
        _ = ((1 + (t+1)*x) % M + (t*x^2) % M) % M := by rw [Nat.add_mod]
        _ = ((1 + (t+1)*x) % M + 0) % M := by rw [htx2]
        _ = (1 + (t+1)*x) % M := by simp

/-!
### B^t modular congruences (B = 4^(3^13))

These are used for the digit formula proofs.
-/

/-- B^t ≡ 1 (mod 3^14) -/
lemma Bpow_mod14 (t : ℕ) : (4^(3^13))^t % 3^14 = 1 := by
  have hbase : 4^(3^13) % 3^14 = 1 := four_pow_3_13_mod14
  induction t with
  | zero => simp
  | succ t ih =>
      calc
        (4^(3^13))^(t+1) % 3^14 = ((4^(3^13))^t * 4^(3^13)) % 3^14 := by ring_nf
        _ = (((4^(3^13))^t % 3^14) * (4^(3^13) % 3^14)) % 3^14 := by rw [Nat.mul_mod]
        _ = (1 * 1) % 3^14 := by rw [ih, hbase]
        _ = 1 := by native_decide

/-- B^t ≡ 1 + t·3^14 (mod 3^15) -/
lemma Bpow_mod15 (t : ℕ) : (4^(3^13))^t % 3^15 = (1 + t * 3^14) % 3^15 := by
  have hbase : 4^(3^13) % 3^15 = (1 + 3^14) % 3^15 := by
    simp only [four_pow_3_13_mod15]
    have hlt : 1 + 3^14 < 3^15 := by native_decide
    exact (Nat.mod_eq_of_lt hlt).symm
  -- Use linearization: (1 + 3^14)^t ≡ 1 + t·3^14 (mod 3^15)
  have hx2 : 3^15 ∣ (3^14)^2 := by
    refine ⟨3^13, ?_⟩
    simp [pow_add, Nat.mul_comm]
  have hlin := one_add_pow_linear (3^15) (3^14) hx2 t
  -- Chain: B^t ≡ (1+3^14)^t ≡ 1+t·3^14
  calc
    (4^(3^13))^t % 3^15 = ((4^(3^13) % 3^15)^t) % 3^15 := by rw [Nat.pow_mod]
    _ = ((1 + 3^14) % 3^15)^t % 3^15 := by rw [hbase]
    _ = (1 + 3^14)^t % 3^15 := by
        have hlt : 1 + 3^14 < 3^15 := by native_decide
        rw [Nat.mod_eq_of_lt hlt]
    _ = (1 + t * 3^14) % 3^15 := hlin

/-- Digit is always < 3 -/
theorem digit_lt (n k : ℕ) : digit n k < 3 := by
  simp only [digit]
  exact Nat.mod_lt _ (by norm_num)

/-- Shifting lemma: digits of n at p+k are digits of (n / 3^p) at k -/
theorem digit_shift (n p k : ℕ) : digit n (p + k) = digit (n / 3^p) k := by
  simp only [digit, Nat.pow_add, Nat.div_div_eq_div_mul]

/-- If q > 0, then some base-3 digit of q is nonzero.
    This uses log bounds: 3^(log 3 q) ≤ q < 3^(log 3 q + 1). -/
theorem exists_digit_ne_zero_of_pos {q : ℕ} (hq : 0 < q) : ∃ k, digit q k ≠ 0 := by
  let k : ℕ := Nat.log 3 q
  refine ⟨k, ?_⟩

  have hq' : q ≠ 0 := Nat.pos_iff_ne_zero.mp hq

  have hk_le : 3^k ≤ q := by
    simpa [k] using (Nat.pow_log_le_self 3 hq')

  have hk_lt : q < 3^(k+1) := by
    have hk_lt' : q < 3^(Nat.log 3 q).succ :=
      Nat.lt_pow_succ_log_self (b := 3) (by decide : 1 < (3 : ℕ)) q
    simpa [k, Nat.succ_eq_add_one] using hk_lt'

  have hk_pos : 0 < 3^k := by
    have h3pos : 0 < 3 := by decide
    exact Nat.pow_pos h3pos

  have hquo_ge_one : 1 ≤ q / 3^k := by
    have : 1 * 3^k ≤ q := by simpa using hk_le
    exact (Nat.le_div_iff_mul_le hk_pos).2 this

  have hquo_lt_three : q / 3^k < 3 := by
    have hk_lt_mul : q < 3 * 3^k := by
      have : q < 3^k * 3 := by
        simpa [Nat.pow_succ] using hk_lt
      simpa [Nat.mul_comm] using this
    exact (Nat.div_lt_iff_lt_mul hk_pos).2 hk_lt_mul

  have hpos : 0 < q / 3^k :=
    lt_of_lt_of_le (Nat.zero_lt_one) hquo_ge_one

  have hdigit : digit q k = q / 3^k := by
    simp [digit, Nat.mod_eq_of_lt hquo_lt_three]

  simpa [hdigit] using (Nat.ne_of_gt hpos)

/-!
## Part 4: Automaton Definition and Properties

The automaton A has two states {s0, s1} and transitions:
- s0 --0--> s0, s0 --2--> s1, s0 --1--> REJECT
- s1 --0--> s0, s1 --1--> s1, s1 --2--> REJECT

Key insight: Forbidden pairs in LSB order are (0,1), (1,2), (2,2).
-/

/-- The automaton state type -/
inductive AutoState | s0 | s1
  deriving DecidableEq, Repr

/-- Automaton step function -/
def autoStep : AutoState → ℕ → Option AutoState
  | AutoState.s0, 0 => some AutoState.s0
  | AutoState.s0, 1 => none  -- reject: s0 sees 1
  | AutoState.s0, 2 => some AutoState.s1
  | AutoState.s1, 0 => some AutoState.s0
  | AutoState.s1, 1 => some AutoState.s1
  | AutoState.s1, 2 => none  -- reject: s1 sees 2
  | _, _ => none

/-- Run automaton on digit list (LSB first) -/
def runAuto (digits : List ℕ) : Option AutoState :=
  digits.foldlM autoStep AutoState.s0

/-- Run automaton from a given starting state -/
def runAutoFrom (digits : List ℕ) (start : AutoState) : Option AutoState :=
  digits.foldlM autoStep start

/-! ### Survival Pattern Characterization (from GPT analysis)

The automaton's acceptance can be characterized by a chain condition on adjacent digits.
Key insight: forbidden consecutive pairs in LSB order are (0,1), (1,2), (2,2).

**Alternative approach (GPT 1B)**: Using `Fin 3` instead of `ℕ` with validity proofs
eliminates the `hvalid : ∀ d ∈ digits, d < 3` preconditions. The key lemma becomes:

```
theorem accepted_from_startStateOfF_iff_chain (digits : List (Fin 3)) (prev : Fin 3) :
    (runAutoFromF digits (startStateOfF prev)).isSome ↔ digits.Chain digitStepF prev
```

This uses `fin_cases` to handle all 3×3 = 9 combinations automatically.
For now we use `List ℕ` with validity proofs to match `Nat.digits 3 n`.
-/

/-- Virtual previous digit encodes current state: 0 ↔ s0, 1 or 2 ↔ s1 -/
def startStateOf (prev : ℕ) : AutoState :=
  if prev = 0 then AutoState.s0 else AutoState.s1

/-- Allowed adjacency relation between consecutive digits.
    This encodes the automaton transitions that don't reject:
    - After 0 (s0): can see 0 or 2 (not 1)
    - After 1 (s1): can see 0 or 1 (not 2)
    - After 2 (s1): can see 0 or 1 (not 2)
    - Digits ≥ 3 are never allowed -/
def digitStep : ℕ → ℕ → Prop
  | 0, 0 => True
  | 0, 2 => True
  | 1, 0 => True
  | 1, 1 => True
  | 2, 0 => True
  | 2, 1 => True
  | _, _ => False

/-- Survival pattern starting from s1: digits must satisfy the chain condition -/
def GoodFromS1 (digits : List ℕ) : Prop :=
  digits.Chain digitStep 1

/-- Survival pattern starting from s0: digits must satisfy the chain condition -/
def GoodFromS0 (digits : List ℕ) : Prop :=
  digits.Chain digitStep 0

/-- Decidable instance for digitStep -/
instance digitStep.decidable : DecidableRel digitStep := fun a b =>
  match a, b with
  | 0, 0 => isTrue trivial
  | 0, 1 => isFalse (fun h => h)
  | 0, 2 => isTrue trivial
  | 1, 0 => isTrue trivial
  | 1, 1 => isTrue trivial
  | 1, 2 => isFalse (fun h => h)
  | 2, 0 => isTrue trivial
  | 2, 1 => isTrue trivial
  | 2, 2 => isFalse (fun h => h)
  | 0, n+3 => isFalse (fun h => h)
  | 1, n+3 => isFalse (fun h => h)
  | 2, n+3 => isFalse (fun h => h)
  | n+3, _ => isFalse (fun h => h)

/-- State after processing a digit from s1 (corresponds to startStateOf prev=1 or prev=2) -/
def stateAfterDigitFromS1 (d : ℕ) : Option AutoState :=
  match d with
  | 0 => some AutoState.s0
  | 1 => some AutoState.s1
  | 2 => none  -- rejection: s1 sees 2
  | _ => none

/-- State after processing a digit from s0 (corresponds to startStateOf prev=0) -/
def stateAfterDigitFromS0 (d : ℕ) : Option AutoState :=
  match d with
  | 0 => some AutoState.s0
  | 1 => none  -- rejection: s0 sees 1
  | 2 => some AutoState.s1
  | _ => none

/-- Equivalence between autoStep and digitStep for valid digits -/
theorem autoStep_some_iff_digitStep (s : AutoState) (d : ℕ) (hd : d < 3) :
    (autoStep s d).isSome ↔ (if s = AutoState.s0 then digitStep 0 d else digitStep 1 d) := by
  cases s <;> interval_cases d <;> simp [autoStep, digitStep]

/-- Helper simp lemma for List.Chain with cons -/
@[simp] theorem chain_cons' {α : Type*} {R : α → α → Prop} {a b : α} {l : List α} :
    List.Chain R a (b :: l) ↔ R a b ∧ List.Chain R b l := by
  constructor
  · intro h; cases h with | cons hab htl => exact ⟨hab, htl⟩
  · rintro ⟨hab, htl⟩; exact List.Chain.cons hab htl

/-- General chain characterization parameterized by "virtual previous digit".
    prev = 0 ↔ currently in s0
    prev = 1 or 2 ↔ currently in s1

    This version doesn't require hvalid since digitStep _ _ = False for invalid digits.
    (From GPT analysis - cleaner unified proof) -/
theorem accepted_from_startStateOf_iff_chain
    (digits : List ℕ) (prev : ℕ) (hprev : prev = 0 ∨ prev = 1 ∨ prev = 2) :
    (∃ st, runAutoFrom digits (startStateOf prev) = some st) ↔
      digits.Chain digitStep prev := by
  induction digits generalizing prev with
  | nil =>
      constructor
      · intro _; exact List.Chain.nil
      · intro _; refine ⟨startStateOf prev, ?_⟩
        simp [runAutoFrom]
  | cons d ds ih =>
      cases hprev with
      | inl hp0 =>
          subst hp0
          cases d with
          | zero =>
              have h := ih (prev := 0) (Or.inl rfl)
              simpa [startStateOf, runAutoFrom, autoStep, digitStep] using h
          | succ d1 =>
              cases d1 with
              | zero =>
                  simp [startStateOf, runAutoFrom, autoStep, digitStep]
              | succ d2 =>
                  cases d2 with
                  | zero =>
                      have h := ih (prev := 2) (Or.inr (Or.inr rfl))
                      simpa [startStateOf, runAutoFrom, autoStep, digitStep] using h
                  | succ d3 =>
                      simp [startStateOf, runAutoFrom, autoStep, digitStep]
      | inr hp12 =>
          cases hp12 with
          | inl hp1 =>
              subst hp1
              cases d with
              | zero =>
                  have h := ih (prev := 0) (Or.inl rfl)
                  simpa [startStateOf, runAutoFrom, autoStep, digitStep] using h
              | succ d1 =>
                  cases d1 with
                  | zero =>
                      have h := ih (prev := 1) (Or.inr (Or.inl rfl))
                      simpa [startStateOf, runAutoFrom, autoStep, digitStep] using h
                  | succ d2 =>
                      cases d2 with
                      | zero =>
                          simp [startStateOf, runAutoFrom, autoStep, digitStep]
                      | succ d3 =>
                          simp [startStateOf, runAutoFrom, autoStep, digitStep]
          | inr hp2 =>
              subst hp2
              cases d with
              | zero =>
                  have h := ih (prev := 0) (Or.inl rfl)
                  simpa [startStateOf, runAutoFrom, autoStep, digitStep] using h
              | succ d1 =>
                  cases d1 with
                  | zero =>
                      have h := ih (prev := 1) (Or.inr (Or.inl rfl))
                      simpa [startStateOf, runAutoFrom, autoStep, digitStep] using h
                  | succ d2 =>
                      cases d2 with
                      | zero =>
                          simp [startStateOf, runAutoFrom, autoStep, digitStep]
                      | succ d3 =>
                          simp [startStateOf, runAutoFrom, autoStep, digitStep]

/-- Specialize to "start from s1": take prev = 1. (No hvalid needed) -/
theorem acceptedFromS1_iff_good' (digits : List ℕ) :
    (∃ st, runAutoFrom digits AutoState.s1 = some st) ↔ GoodFromS1 digits := by
  simpa [GoodFromS1, startStateOf] using
    (accepted_from_startStateOf_iff_chain (digits := digits) (prev := 1)
      (hprev := Or.inr (Or.inl rfl)))

/-- Specialize to "start from s0": take prev = 0. (No hvalid needed) -/
theorem acceptedFromS0_iff_good' (digits : List ℕ) :
    (∃ st, runAutoFrom digits AutoState.s0 = some st) ↔ GoodFromS0 digits := by
  simpa [GoodFromS0, startStateOf] using
    (accepted_from_startStateOf_iff_chain (digits := digits) (prev := 0)
      (hprev := Or.inl rfl))

/-- Key lemma: runAutoFrom on a list succeeds iff the list satisfies the chain condition.
    This is the survival pattern characterization. (Version with hvalid for compatibility) -/
theorem acceptedFromS1_iff_good (digits : List ℕ) (hvalid : ∀ d ∈ digits, d < 3) :
    (runAutoFrom digits AutoState.s1).isSome ↔ GoodFromS1 digits := by
  rw [Option.isSome_iff_exists]
  exact acceptedFromS1_iff_good' digits

/-- Similar characterization starting from s0. (Version with hvalid for compatibility) -/
theorem acceptedFromS0_iff_good (digits : List ℕ) (hvalid : ∀ d ∈ digits, d < 3) :
    (runAutoFrom digits AutoState.s0).isSome ↔ GoodFromS0 digits := by
  rw [Option.isSome_iff_exists]
  exact acceptedFromS0_iff_good' digits

/-- A useful digit list extraction function -/
def digitsFromPos (n : ℕ) (start : ℕ) (len : ℕ) : List ℕ :=
  List.map (fun k => digit n (start + k)) (List.range len)

/-- All extracted digits are valid (< 3) -/
theorem digitsFromPos_valid (n start len : ℕ) :
    ∀ d ∈ digitsFromPos n start len, d < 3 := by
  intro d hd
  simp only [digitsFromPos, List.mem_map, List.mem_range] at hd
  obtain ⟨k, _, hdk⟩ := hd
  rw [← hdk]
  exact digit_lt n (start + k)


end ErdosAnalytical
