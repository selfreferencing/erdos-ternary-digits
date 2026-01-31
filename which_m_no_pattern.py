#!/usr/bin/env python3
"""
Which actual m values give orbit elements without blocking patterns?
"""

def to_base3(n, num_digits=None):
    if n == 0:
        digits = [0]
    else:
        digits = []
        while n > 0:
            digits.append(n % 3)
            n //= 3
    if num_digits:
        while len(digits) < num_digits:
            digits.append(0)
    return digits

def has_pattern(digits):
    for i in range(len(digits) - 1):
        pair = (digits[i], digits[i+1])
        if pair in [(2, 2), (0, 2), (1, 1)]:
            return True
    return False

print("Which m values give 4^m mod 3^k without pattern?")
print("=" * 60)

# For k = 10, find all m in [0, period) where 4^m mod 3^k lacks pattern
for k in [6, 8, 10]:
    period = 3 ** (k - 1)
    check_mod = 3 ** k

    no_pattern_m = []
    val = 1  # 4^0
    for m in range(period):
        digits = to_base3(val, k)
        if not has_pattern(digits):
            no_pattern_m.append(m)
        val = (val * 4) % check_mod

    print(f"\nk = {k} (period = {period}):")
    print(f"  m values without pattern in first {k} digits: {len(no_pattern_m)}")
    print(f"  First 20: {no_pattern_m[:20]}")
    if len(no_pattern_m) > 20:
        print(f"  Last 10: {no_pattern_m[-10:]}")

    # Check: what are the actual 4^m values for small m?
    print(f"\n  Checking actual 4^m for these m:")
    for m in no_pattern_m[:10]:
        actual = 4 ** m
        actual_digits = to_base3(actual)
        has_pat = has_pattern(actual_digits)
        print(f"    4^{m} = {actual_digits[:15]}{'...' if len(actual_digits) > 15 else ''} -> pattern: {has_pat}")

print("\n" + "=" * 60)
print("KEY INSIGHT: Checking if 4^m EVENTUALLY has pattern")
print("=" * 60)

# For each m without pattern in first k digits, does the FULL 4^m have pattern?
print("\nFor m without pattern in first 10 digits, check FULL 4^m:")

k = 10
period = 3 ** (k - 1)
check_mod = 3 ** k

val = 1
no_pattern_m = []
for m in range(period):
    digits = to_base3(val, k)
    if not has_pattern(digits):
        no_pattern_m.append(m)
    val = (val * 4) % check_mod

print(f"\n{len(no_pattern_m)} values of m in [0, {period}) have no pattern in first 10 digits")

# For each, check if FULL 4^m has pattern
full_no_pattern = []
full_has_pattern = []

for m in no_pattern_m:
    actual = 4 ** m
    actual_digits = to_base3(actual)
    if has_pattern(actual_digits):
        full_has_pattern.append(m)
    else:
        full_no_pattern.append(m)

print(f"\nOf these {len(no_pattern_m)} m values:")
print(f"  FULL 4^m has no pattern: {len(full_no_pattern)} -> {full_no_pattern}")
print(f"  FULL 4^m has pattern: {len(full_has_pattern)}")

print("\n" + "=" * 60)
print("THE CRITICAL OBSERVATION")
print("=" * 60)

print("""
The orbit elements without pattern in first k digits are:
- [1, 0, 0, ...]: This is 4^0 = 1. Solution!
- [1, 2, 1, 0, ...]: This is 4^2 mod 3^k. But actual 4^2 = 16 = [1,2,1] which HAS digit 2!

Wait - [1, 2, 1] has no BLOCKING pattern:
- (1, 2): not a blocking pattern
- (2, 1): not a blocking pattern

But 16 = 121₃ DOES have digit 2 in it!

The blocking patterns are about PROPAGATION of digit 2 via multiplication.
Having digit 2 is different from having a blocking pattern.

Let me verify...
""")

# Check: which 4^m values have digit 2 vs have blocking pattern?
print("\nDigit 2 vs Blocking Pattern for 4^m, m = 0 to 10:")
print("-" * 60)
for m in range(11):
    digits = to_base3(4 ** m)
    has_dig2 = 2 in digits
    has_block = has_pattern(digits)
    print(f"  4^{m:2d} = {str(digits):30s} digit_2: {has_dig2}, blocking: {has_block}")

print("\n" + "=" * 60)
print("THE REAL QUESTION")
print("=" * 60)

print("""
For the PROOF, we need:
1. If 4^m has digit 2 AND blocking pattern -> 4^(m+1) has digit 2
2. For m >= 5, 4^m has blocking pattern

The issue is: can 4^m have digit 2 but NO blocking pattern?
If so, it might "recover" (4^(m+1) has no digit 2).

From the table above:
- 4^2 = [1,2,1]: has digit 2, NO blocking pattern -> 4^3 = [1,0,1,2] has digit 2
- 4^3 = [1,0,1,2]: has digit 2, NO blocking pattern -> 4^4 = [1,1,1,0,0,1] NO digit 2!

So 4^3 is the unique case that "recovers"!

For m >= 4, we need to check: does 4^m always have a blocking pattern?
""")

print("\nBlocking pattern status for 4^m, m = 4 to 20:")
for m in range(4, 21):
    digits = to_base3(4 ** m)
    has_block = has_pattern(digits)
    which = []
    for i in range(len(digits) - 1):
        pair = (digits[i], digits[i+1])
        if pair == (1, 1):
            which.append(f"C@{i}")
        elif pair == (2, 2):
            which.append(f"A@{i}")
        elif pair == (0, 2):
            which.append(f"B@{i}")
    print(f"  4^{m:2d}: {has_block} -> {which[:5]}")
