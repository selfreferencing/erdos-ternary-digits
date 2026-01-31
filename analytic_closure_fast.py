#!/usr/bin/env python3
"""
Fast version: Find K such that all orbit elements mod 3^K have blocking pattern.
"""

def to_base3(n, num_digits):
    digits = []
    for _ in range(num_digits):
        digits.append(n % 3)
        n //= 3
    return digits

def has_pattern(digits):
    """Check if digits contain blocking pattern."""
    for i in range(len(digits) - 1):
        pair = (digits[i], digits[i+1])
        if pair in [(2, 2), (0, 2), (1, 1)]:
            return True
    return False

print("Checking orbit {4^m mod 3^k} for blocking patterns")
print("=" * 60)

# For each k, check if ALL orbit elements have patterns
for k in range(3, 20):
    check_mod = 3 ** k

    # Generate orbit by repeated multiplication
    val = 1
    no_pattern_found = False
    no_pattern_example = None
    orbit_size = 0

    seen = set()
    while val not in seen:
        seen.add(val)
        orbit_size += 1

        digits = to_base3(val, k)
        if not has_pattern(digits):
            no_pattern_found = True
            no_pattern_example = (val, digits)

        val = (val * 4) % check_mod

    if no_pattern_found:
        print(f"k={k:2d}: ✗ Orbit has {orbit_size} elements, some lack pattern")
        print(f"       Example: {no_pattern_example[1]}")
    else:
        print(f"k={k:2d}: ✓ ALL {orbit_size} orbit elements have pattern!")
        print(f"\n*** CRITICAL K FOUND: k = {k} ***")
        print(f"Every 4^m mod 3^{k} has a blocking pattern in first {k} digits.")
        print("This gives a complete analytic proof!")
        break
