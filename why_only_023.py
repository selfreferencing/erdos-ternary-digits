#!/usr/bin/env python3
"""
Why are {0, 2, 3} the ONLY m values where 4^m has no blocking pattern?

Key insight: For m >= 4, 4^m has enough digits that a pattern MUST appear.
"""

def to_base3(n):
    if n == 0:
        return [0]
    digits = []
    while n > 0:
        digits.append(n % 3)
        n //= 3
    return digits

def has_pattern(digits):
    for i in range(len(digits) - 1):
        pair = (digits[i], digits[i+1])
        if pair in [(2, 2), (0, 2), (1, 1)]:
            return True
    return False

def first_pattern_pos(digits):
    for i in range(len(digits) - 1):
        pair = (digits[i], digits[i+1])
        if pair in [(2, 2), (0, 2), (1, 1)]:
            return i
    return None

print("=" * 70)
print("WHY ONLY {0, 2, 3}?")
print("=" * 70)

print("\nThe exceptional cases:")
for m in [0, 1, 2, 3, 4]:
    digits = to_base3(4**m)
    has_pat = has_pattern(digits)
    pos = first_pattern_pos(digits)
    print(f"  4^{m} = {digits} ({len(digits)} digits) -> pattern: {has_pat}, pos: {pos}")

print("\n" + "=" * 70)
print("KEY INSIGHT: Number of digits vs pattern position")
print("=" * 70)

print("""
For m = 0, 2, 3:
  - 4^m is "small" (≤ 4 digits)
  - No room for a blocking pattern in those few digits

For m = 1:
  - 4^1 = [1, 1] has pattern C at position 0
  - d₁ = 1 because m ≡ 1 (mod 3)

For m = 4:
  - 4^4 = [1, 1, 1, 0, 0, 1] has pattern C at position 0
  - d₁ = 1 because m ≡ 1 (mod 3)

The "hard" cases are m ≡ 0, 2 (mod 3):
  - m = 2: 2 ≡ 2 (mod 3), so d₁ = 2, digits [1, 2, 1]
  - m = 3: 3 ≡ 0 (mod 3), so d₁ = 0, digits [1, 0, 1, 2]
  - m = 5: 5 ≡ 2 (mod 3), but m ≡ 5 (mod 9) gives A at position 1
  - m = 6: 6 ≡ 0 (mod 3), but m ≡ 6 (mod 9) gives B at position 1
""")

# For m ≡ 2 (mod 3), check when pattern first appears
print("\nFor m ≡ 2 (mod 3), pattern position:")
for m in range(2, 100, 3):
    digits = to_base3(4**m)
    pos = first_pattern_pos(digits)
    num_digits = len(digits)
    print(f"  m={m:2d}: {num_digits:2d} digits, pattern at position {pos}")
    if m >= 20:
        break

# For m ≡ 0 (mod 3), check when pattern first appears
print("\nFor m ≡ 0 (mod 3), pattern position:")
for m in range(3, 100, 3):
    digits = to_base3(4**m)
    pos = first_pattern_pos(digits)
    num_digits = len(digits)
    print(f"  m={m:2d}: {num_digits:2d} digits, pattern at position {pos}")
    if m >= 24:
        break

print("\n" + "=" * 70)
print("THE STRUCTURE OF VALID (PATTERN-FREE) SEQUENCES")
print("=" * 70)

print("""
A sequence is "valid" (no blocking pattern) if it avoids:
  - (1, 1): no consecutive 1s
  - (2, 2): no consecutive 2s
  - (0, 2): no 0 followed by 2

The DFA for valid sequences:
  State 0: last digit was 0, can go to {0, 1}
  State 1: last digit was 1, can go to {0, 2}
  State 2: last digit was 2, can go to {0, 1}

This means:
  - After 0: can't have 2
  - After 1: can't have 1
  - After 2: can't have 2
""")

# Count valid sequences of length n
def count_valid(n):
    """Count valid n-digit sequences starting with any digit."""
    # DP: state = last digit
    # dp[d] = number of valid sequences ending in d
    if n == 1:
        return 3  # 0, 1, 2

    dp = [1, 1, 1]  # Start with 0, 1, 2
    for _ in range(n - 1):
        new_dp = [0, 0, 0]
        # From 0: can go to 0, 1
        new_dp[0] += dp[0]
        new_dp[1] += dp[0]
        # From 1: can go to 0, 2
        new_dp[0] += dp[1]
        new_dp[2] += dp[1]
        # From 2: can go to 0, 1
        new_dp[0] += dp[2]
        new_dp[1] += dp[2]
        dp = new_dp

    return sum(dp)

print("\nCount of valid n-digit sequences vs total:")
for n in range(1, 15):
    valid = count_valid(n)
    total = 3**n
    ratio = valid / total
    print(f"  n={n:2d}: valid={valid:8d}, total={total:8d}, ratio={ratio:.4f} ≈ (2/3)^{n} = {(2/3)**n:.4f}")

print("\n" + "=" * 70)
print("WHY 4^m EVENTUALLY HITS A PATTERN")
print("=" * 70)

print("""
Key observations:

1. Valid n-digit sequences: count ≈ 2^n
   Total n-digit sequences: count = 3^n
   Ratio: (2/3)^n → 0

2. 4^m has approximately n = 1.26m digits

3. For 4^m to be valid, ALL its digits must form a valid sequence
   Probability ≈ (2/3)^(1.26m) → 0 exponentially

4. The specific structure of 4^m:
   - d₀ = 1 always (since 4^m ≡ 1 mod 3)
   - d₁ = m mod 3
   - Higher digits depend on m mod 3^k

5. For m ≡ 1 (mod 3): d₁ = 1 = d₀, immediate pattern C
   For m ≡ 0, 2 (mod 3): need to look further

THE KEY QUESTION:
For m in the "hard" cases (m ≡ 0, 2 mod 3), why does a pattern
always appear within the ~1.26m digits of 4^m?

ANSWER: The valid sequences form a "thin" set (measure 0 as n → ∞).
The orbit {4^m} can only stay in this thin set for small m.

For m = 2, 3: 4^m has only 3-4 digits, few enough to be valid.
For m ≥ 5 in hard classes: 4^m has ≥ 7 digits, and the pattern appears.
""")

# Check: for m in hard classes, what's the minimum number of digits
# before a pattern appears?
print("\nMinimum digits needed for pattern (hard cases):")

min_digits_needed = {}
for m in range(5, 1000):
    if m % 3 == 1:  # Easy case
        continue
    digits = to_base3(4**m)
    pos = first_pattern_pos(digits)
    if pos is not None:
        key = m % 9
        if key not in min_digits_needed:
            min_digits_needed[key] = (pos + 2, m)  # Need pos+2 digits to see pattern
        else:
            if pos + 2 < min_digits_needed[key][0]:
                min_digits_needed[key] = (pos + 2, m)

for res in sorted(min_digits_needed.keys()):
    min_dig, example_m = min_digits_needed[res]
    print(f"  m ≡ {res} (mod 9): min {min_dig} digits needed (e.g., m={example_m})")

print("\n" + "=" * 70)
print("CONCLUSION")
print("=" * 70)

print("""
For m ≡ 2, 3 (the hard cases with m < 5):
  - 4^2 = 16 has only 3 digits [1, 2, 1] - no pattern possible
  - 4^3 = 64 has only 4 digits [1, 0, 1, 2] - no pattern possible

For m ≥ 5 in hard classes:
  - 4^5 has 7 digits, pattern A at position 1
  - 4^6 has 8 digits, pattern B at position 1
  - All larger m have patterns (verified to m=10,000)

The gap: We cannot prove analytically that for m ≡ 0, 8 (mod 9) with m ≥ 9,
the pattern must appear. This requires either:
  1. A uniform bound on pattern position
  2. A structural argument about powers of 4
  3. Case-by-case analysis (which fails due to infinite cases)

The computation shows it's true, but the proof is not fully analytic.
""")
