#!/usr/bin/env python3
"""
Verify the persistence of digit 2 through powers of 4.

Key question: Once 4^m has digit 2, do all 4^{m+k} for k >= 0 have digit 2?

Counter-example found: 4^3 = 64 has digit 2, but 4^4 = 256 does NOT!

So the simple persistence lemma is FALSE. We need a more nuanced argument.
"""

def to_base3(n):
    if n == 0:
        return [0]
    digits = []
    while n > 0:
        digits.append(n % 3)
        n //= 3
    return digits

def has_digit_2(n):
    while n > 0:
        if n % 3 == 2:
            return True
        n //= 3
    return False

def to_base3_str(n):
    return ''.join(map(str, reversed(to_base3(n))))

print("=" * 70)
print("POWERS OF 4 AND DIGIT 2 PRESENCE")
print("=" * 70)

print("\nChecking 4^m for m = 0 to 20:")
print()

chain = []
for m in range(21):
    power = 4 ** m
    has_2 = has_digit_2(power)
    b3 = to_base3_str(power)
    marker = "✗ (has 2)" if has_2 else "✓ (no 2)"
    chain.append(has_2)
    print(f"  4^{m:2d} = {power:15d} = {b3:30s} {marker}")

print("\n" + "=" * 70)
print("ANALYSIS OF DIGIT 2 PATTERN")
print("=" * 70)

# Find the pattern
print("\nDigit 2 presence pattern (True = has digit 2):")
print("m:  ", end="")
for m in range(21):
    print(f"{m:2d} ", end="")
print()
print("has:", end="")
for h in chain:
    print(" ✗ " if h else " ✓ ", end="")
print()

# Find gaps (m where 4^m has no digit 2)
gaps = [m for m, h in enumerate(chain) if not h]
print(f"\nValues of m where 4^m has no digit 2: {gaps}")
print(f"Corresponding n = 2m: {[2*m for m in gaps]}")

# Check if persistence holds after 256
print("\n" + "=" * 70)
print("DOES DIGIT 2 PERSIST AFTER 256?")
print("=" * 70)

print("\nChecking 4^m for m = 4 to 50:")
all_have_2_after_4 = True
first_fail = None
for m in range(5, 51):
    power = 4 ** m
    if not has_digit_2(power):
        print(f"  COUNTER-EXAMPLE: 4^{m} = {power} has no digit 2!")
        print(f"  Base 3: {to_base3_str(power)}")
        all_have_2_after_4 = False
        first_fail = m
        break

if all_have_2_after_4:
    print("  All 4^m for m in [5, 50] have digit 2. ✓")

# The actual pattern
print("\n" + "=" * 70)
print("THE ACTUAL STRUCTURE")
print("=" * 70)

print("""
The digit 2 pattern for powers of 4:
  m=0: ✓ (1)
  m=1: ✓ (4)
  m=2: ✗ (16 = 121₃)
  m=3: ✗ (64 = 2101₃)
  m=4: ✓ (256 = 100111₃) <-- RECOVERY!
  m≥5: ✗ (all have digit 2)

Key insight: 64 → 256 "recovers" from digit 2!
But 256 → 1024 does NOT recover.

The question is: WHY does 64 → 256 recover, but 256 → 1024 doesn't?
""")

# Trace the 64 → 256 multiplication carefully
print("\n" + "=" * 70)
print("TRACING 64 × 4 = 256")
print("=" * 70)

print("\n64 = 2101₃ = [1, 0, 1, 2] (LSB first)")
print("Let's trace 4 × 64 by hand:")
print()
print("64 in base 3: 2 1 0 1 (MSB to LSB)")
print()
print("Multiplication by 4 = 1 + 3:")
print("  64 =         2 1 0 1")
print("  + 3×64 =   2 1 0 1 0  (shifted)")
print("  ─────────────────────")
print("  Result needs carry propagation...")
print()

# Do it carefully
digits = to_base3(64)  # [1, 0, 1, 2] LSB first
print(f"64 digits (LSB first): {digits}")

# 4 × 64 = 64 + 3×64
# In base 3, this is: add digits[i] + digits[i-1] with carry

result = []
carry = 0
for i in range(len(digits) + 1):
    d_i = digits[i] if i < len(digits) else 0
    d_prev = digits[i-1] if i > 0 and i-1 < len(digits) else 0

    total = d_i + d_prev + carry
    out = total % 3
    carry = total // 3
    result.append(out)
    print(f"  pos {i}: d_i={d_i}, d_prev={d_prev}, carry_in={carry - total//3 + total//3}, sum={total}, out={out}, carry_out={carry}")

# Remove trailing zeros
while result and result[-1] == 0:
    result.pop()

print(f"\nResult: {result} (LSB first)")
print(f"As number: {sum(d * 3**i for i, d in enumerate(result))}")
print(f"Expected: 256")
print(f"Has digit 2: {2 in result}")

# Now trace 256 × 4 = 1024
print("\n" + "=" * 70)
print("TRACING 256 × 4 = 1024")
print("=" * 70)

digits_256 = to_base3(256)  # [1, 1, 1, 0, 0, 1] LSB first
print(f"256 digits (LSB first): {digits_256}")

result_1024 = []
carry = 0
for i in range(len(digits_256) + 2):
    d_i = digits_256[i] if i < len(digits_256) else 0
    d_prev = digits_256[i-1] if i > 0 and i-1 < len(digits_256) else 0

    total = d_i + d_prev + carry
    out = total % 3
    new_carry = total // 3
    result_1024.append(out)
    print(f"  pos {i}: d_i={d_i}, d_prev={d_prev}, carry_in={carry}, sum={total}, out={out}, carry_out={new_carry}")
    carry = new_carry

# Remove trailing zeros
while result_1024 and result_1024[-1] == 0:
    result_1024.pop()

print(f"\nResult: {result_1024} (LSB first)")
print(f"As number: {sum(d * 3**i for i, d in enumerate(result_1024))}")
print(f"Expected: 1024 = {to_base3(1024)}")
print(f"Has digit 2: {2 in result_1024}")

print("\n" + "=" * 70)
print("THE KEY DIFFERENCE")
print("=" * 70)

print("""
Why 64 → 256 avoids digit 2:
  64 = [1, 0, 1, 2] (LSB first)
  The '2' at position 3 is "isolated" - preceded by 1, followed by nothing
  When multiplying, the carries resolve without creating output 2

Why 256 → 1024 creates digit 2:
  256 = [1, 1, 1, 0, 0, 1] (LSB first)
  Position 1: d_i=1, d_prev=1, carry=0 → sum=2 → OUTPUT 2!

The consecutive 1s in 256 are the killer!
""")
