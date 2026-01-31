#!/usr/bin/env python3
"""
Complete conservation law: Every 4^m for m >= 5 has at least one of:
  - Adjacent 2s (22)
  - Consecutive 1s (11)
  - (0, 2) pair

Each of these blocks recovery:
  - Adjacent 2s → violates condition (a)
  - Consecutive 1s → violates condition (c)
  - (0, 2) pair → violates condition (b)
"""

def to_base3(n):
    if n == 0: return [0]
    digits = []
    while n > 0:
        digits.append(n % 3)
        n //= 3
    return digits

def has_adjacent_2s(n):
    digits = to_base3(n)
    return any(digits[i] == 2 and digits[i+1] == 2 for i in range(len(digits)-1))

def has_consecutive_1s(n):
    digits = to_base3(n)
    return any(digits[i] == 1 and digits[i+1] == 1 for i in range(len(digits)-1))

def has_02_pair(n):
    digits = to_base3(n)
    return any((digits[i], digits[i+1]) == (0, 2) for i in range(len(digits)-1))

def has_blocking_pattern(n):
    return has_adjacent_2s(n) or has_consecutive_1s(n) or has_02_pair(n)

print("=" * 80)
print("COMPLETE CONSERVATION LAW")
print("=" * 80)

print("""
THEOREM: For m >= 5, 4^m has at least one of:
  (A) Adjacent 2s (positions i, i+1 both have digit 2)
  (B) (0, 2) pair (position i has 0, position i+1 has 2)
  (C) Consecutive 1s (positions i, i+1 both have digit 1)

Each blocks recovery:
  (A) → digit 2 at position i is in context (..., 2, 2) → not (d, 2, 0)
  (B) → creates digit 2 in output at position i+1 (sum = 0 + 2 + carry = 2)
  (C) → creates digit 2 in output at position i+1 (sum = 1 + 1 + 0 = 2)
""")

# Verify for m = 5 to 10000
counterexamples = []
for m in range(5, 10001):
    power = 4 ** m
    if not has_blocking_pattern(power):
        counterexamples.append(m)

print(f"Checked 4^m for m = 5 to 10000")
print(f"Counterexamples: {counterexamples if counterexamples else 'NONE'}")
print()

if not counterexamples:
    print("✓ CONSERVATION LAW VERIFIED to m = 10000")
    print()

# Analyze which pattern is primary
print("\n" + "=" * 80)
print("BREAKDOWN BY PATTERN")
print("=" * 80)

only_A = 0  # only adjacent 2s
only_B = 0  # only 02 pair
only_C = 0  # only consecutive 1s
multiple = 0

for m in range(5, 1001):
    power = 4 ** m
    A = has_adjacent_2s(power)
    B = has_02_pair(power)
    C = has_consecutive_1s(power)

    count = sum([A, B, C])
    if count == 1:
        if A: only_A += 1
        elif B: only_B += 1
        else: only_C += 1
    else:
        multiple += 1

total = 996
print(f"m = 5 to 1000 ({total} powers):")
print(f"  Only adjacent 2s: {only_A} ({100*only_A/total:.1f}%)")
print(f"  Only (0,2) pair: {only_B} ({100*only_B/total:.1f}%)")
print(f"  Only consecutive 1s: {only_C} ({100*only_C/total:.1f}%)")
print(f"  Multiple patterns: {multiple} ({100*multiple/total:.1f}%)")

# THE FORMAL PROOF
print("\n" + "=" * 80)
print("THE FORMAL PROOF STRUCTURE")
print("=" * 80)

print("""
THEOREM: Only n ∈ {0, 2, 8} have 2^n with no digit 2 in base 3.

PROOF:

1. Odd n: 2^n ≡ 2 (mod 3), so last digit is 2. ✓

2. Even n = 2m: Need 4^m to have no digit 2.

3. Small cases:
   - m = 0: 4^0 = 1 ✓
   - m = 1: 4^1 = 4 = 11₃ ✓
   - m = 2: 4^2 = 16 = 121₃ has digit 2 ✗
   - m = 3: 4^3 = 64 = 2101₃ has digit 2 ✗
   - m = 4: 4^4 = 256 = 100111₃ ✓ (but has consecutive 1s)

4. Base case for trap:
   4^4 = 256 has consecutive 1s at positions 0, 1, 2.
   → 4^5 = 1024 has digit 2 at positions 1, 2.
   → 4^5 also has adjacent 2s at positions 1, 2.

5. CONSERVATION LEMMA: For m >= 5, 4^m has at least one of:
   (A) adjacent 2s, (B) (0,2) pair, or (C) consecutive 1s.

   Verified computationally to m = 10000 with zero counterexamples.

6. BLOCKING LEMMA: Each pattern blocks recovery:
   (A) Adjacent 2s → digit 2 context is (?, 2, 2), not (d, 2, 0)
   (B) (0, 2) pair → at position of 2: sum = 2 + 0 + carry ≥ 2 → digit 2
   (C) Consecutive 1s → sum = 1 + 1 + 0 = 2 → digit 2

7. Therefore: For m >= 5, 4^m has digit 2, and 4^(m+1) has digit 2.

CONCLUSION: Solutions are m ∈ {0, 1, 4}, giving n ∈ {0, 2, 8}. ∎
""")

# THE GAP
print("\n" + "=" * 80)
print("THE REMAINING GAP")
print("=" * 80)

print("""
The proof is COMPLETE except for the Conservation Lemma (step 5).

The lemma is VERIFIED to m = 10000 but not proven analytically.

An analytic proof would require showing that one of (A), (B), (C)
must always occur in the base-3 digits of 4^m for m >= 5.

POSSIBLE APPROACHES:

1. Show that NOT having any of (A), (B), (C) is a severe constraint:
   - No adjacent 2s → 2s are "isolated"
   - No (0, 2) pairs → 2 is never preceded by 0
   - No consecutive 1s → 1s are "isolated"

   Combined constraint: Every 2 is preceded by 1 or 2, every 1 is not
   adjacent to another 1. This limits digit patterns severely.

2. Use 3-adic analysis: Show 4^m mod 3^k has structure forcing (A), (B), or (C).

3. Prove by contradiction: Assume 4^m has no (A), (B), or (C). Show this
   leads to a contradiction with 4^m being a power of 4.

The constraint is so severe that we conjecture no such number exists
beyond 4^4 = 256, but proving this requires deeper analysis.
""")

# Final check: what's the last power without (A), (B), or (C)?
print("\n" + "=" * 80)
print("HISTORICAL CHECK: When do patterns start?")
print("=" * 80)

for m in range(20):
    power = 4 ** m
    A = has_adjacent_2s(power)
    B = has_02_pair(power)
    C = has_consecutive_1s(power)

    patterns = []
    if A: patterns.append('A')
    if B: patterns.append('B')
    if C: patterns.append('C')

    digits = to_base3(power)
    print(f"4^{m:2d} = {digits}: {patterns if patterns else 'NONE'}")
